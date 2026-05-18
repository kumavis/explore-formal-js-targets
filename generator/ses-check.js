#!/usr/bin/env node
'use strict';
// SES (Hardened JavaScript / Agoric Endo) compatibility evaluator.
//
// For each implementation we run three orthogonal checks:
//
//   1. Static scan — search the generated JS for patterns the SES doc
//      flags as incompatible: eval / new Function, assignment to
//      primordials, sloppy-mode-only idioms, etc.
//
//   2. lockdown + require — spawn a fresh node, import 'ses', call
//      lockdown(), then require() the entry file. This is the most
//      forgiving check: globals are frozen but the loader still works.
//
//   3. Compartment evaluate — read the entry file as source, evaluate
//      it inside a SES Compartment with endowments {console}. This is
//      the strictest realistic deployment shape.

const fs = require('node:fs');
const path = require('node:path');
const { spawnSync } = require('node:child_process');
const { PROBLEMS, ROOT } = require('./problems.js');

const OUT_ROOT = path.join(ROOT, 'outputs');
const NODE_PATH_FOR_NPM = path.join(ROOT, 'node_modules');

const STATIC_PATTERNS = [
  { id: 'eval-call',         regex: /\beval\s*\(/g,              desc: 'eval() call' },
  { id: 'new-function',      regex: /\bnew\s+Function\s*\(/g,    desc: 'new Function(...)' },
  { id: 'with-stmt',         regex: /\bwith\s*\(/g,              desc: 'with (...) {}' },
  { id: 'proto-prop',        regex: /__proto__/g,                 desc: '__proto__' },
  { id: 'mut-array-proto',   regex: /Array\.prototype\.\w+\s*=/g, desc: 'Array.prototype.X =' },
  { id: 'mut-obj-proto',     regex: /Object\.prototype\.\w+\s*=/g, desc: 'Object.prototype.X =' },
  { id: 'mut-string-proto',  regex: /String\.prototype\.\w+\s*=/g, desc: 'String.prototype.X =' },
  { id: 'global-assign',     regex: /\bglobalThis\.\w+\s*=/g,    desc: 'globalThis.X =' },
  { id: 'bare-globals',      regex: /\b(?:global|window)\.\w+\s*=/g, desc: 'global.X =' },
];

function staticScan(jsFiles) {
  const findings = [];
  for (const f of jsFiles) {
    if (!f.content) continue;
    for (const p of STATIC_PATTERNS) {
      p.regex.lastIndex = 0;
      const matches = f.content.match(p.regex);
      if (matches && matches.length > 0) {
        findings.push({ file: f.relPath, id: p.id, desc: p.desc, count: matches.length });
      }
    }
  }
  return findings;
}

function runProbe(driverSource, cwd, env) {
  const res = spawnSync(
    process.execPath,
    ['-e', driverSource],
    {
      cwd,
      env: { ...process.env, ...env },
      encoding: 'utf8',
      maxBuffer: 32 * 1024 * 1024,
      timeout: 20000,
    },
  );
  return {
    exitCode: res.status,
    stdout: (res.stdout || '').slice(0, 8192),
    stderr: (res.stderr || '').slice(0, 8192),
    timedOut: res.signal === 'SIGTERM',
  };
}

function lockdownRequireProbe(impl) {
  const entryRel = path.relative(impl.outputDir, impl.jsEntry);
  // Some Dafny outputs need bignumber.js from project node_modules; pass via NODE_PATH.
  // Agda needs its emit dir on NODE_PATH for sibling jAgda.X.js lookups.
  const nodePathParts = [NODE_PATH_FOR_NPM, impl.outputDir].join(':');
  const driver = `
    process.env.NODE_PATH = ${JSON.stringify(nodePathParts)};
    require('node:module').Module._initPaths();
    require('ses');
    try {
      lockdown({ errorTaming: 'unsafe' });
    } catch (e) {
      console.error('LOCKDOWN_FAILED:', e && e.message);
      process.exit(2);
    }
    try {
      require(${JSON.stringify('./' + entryRel)});
      console.log('OK');
    } catch (e) {
      console.error('REQUIRE_FAILED:', (e && e.message) || String(e));
      process.exit(3);
    }
  `;
  return runProbe(driver, impl.outputDir, {});
}

function compartmentEvaluateProbe(impl) {
  const entryAbs = impl.jsEntry;
  // Skip if there are sibling requires we can't satisfy.
  const driver = `
    require('ses');
    lockdown({ errorTaming: 'unsafe' });
    const fs = require('node:fs');
    const src = fs.readFileSync(${JSON.stringify(entryAbs)}, 'utf8');
    const c = new Compartment({
      console,
      process: harden({ stdout: { write: (s) => process.stdout.write(s) } }),
    });
    try {
      c.evaluate(src);
      console.log('OK');
    } catch (e) {
      console.error('EVALUATE_FAILED:', (e && e.message) || String(e));
      process.exit(4);
    }
  `;
  return runProbe(driver, impl.outputDir, {});
}

function classify(probe) {
  if (probe.exitCode === 0) return 'pass';
  if (probe.timedOut) return 'timeout';
  if (probe.stderr.includes('LOCKDOWN_FAILED')) return 'lockdown-failed';
  if (probe.stderr.includes('REQUIRE_FAILED')) return 'require-failed';
  if (probe.stderr.includes('EVALUATE_FAILED')) return 'evaluate-failed';
  return 'crashed';
}

function evaluateProblem(problemId) {
  const probDir = path.join(OUT_ROOT, problemId);
  const data = JSON.parse(fs.readFileSync(path.join(probDir, 'results.json'), 'utf8'));
  for (const r of data.results) {
    process.stderr.write(`  [${data.problem.id}/${r.language}] `);
    const impl = data.problem.implementations.find((i) => i.language === r.language);

    const stat = staticScan(r.compiled || []);
    process.stderr.write(`static=${stat.length} `);

    const lockReq = lockdownRequireProbe(impl);
    const lockReqClass = classify(lockReq);
    process.stderr.write(`lockdown+require=${lockReqClass} `);

    const compEval = compartmentEvaluateProbe(impl);
    const compEvalClass = classify(compEval);
    process.stderr.write(`compartment=${compEvalClass}\n`);

    r.ses = {
      staticFindings: stat,
      lockdownRequire: { ...lockReq, classification: lockReqClass },
      compartmentEvaluate: { ...compEval, classification: compEvalClass },
    };
  }
  fs.writeFileSync(path.join(probDir, 'results.json'), JSON.stringify(data, null, 2));
}

function main() {
  for (const p of PROBLEMS) {
    process.stderr.write(`\n=== SES ${p.id} ===\n`);
    evaluateProblem(p.id);
  }
  process.stderr.write('\nDone.\n');
}

main();
