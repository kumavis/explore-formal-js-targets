#!/usr/bin/env node
'use strict';
// Generate one markdown doc per problem under docs/<problem-id>.md,
// plus a top-level docs/README.md and docs/EVALUATION.md.

const fs = require('node:fs');
const path = require('node:path');
const { PROBLEMS, ROOT } = require('./problems.js');

const OUT_ROOT = path.join(ROOT, 'outputs');
const DOCS_ROOT = path.join(ROOT, 'docs');

const LANG_FENCE = { Dafny: 'dafny', Agda: 'agda', Idris2: 'idris', JS: 'js' };

// Whether each tool's output uses module-loader `require()` at top level and
// therefore needs a bundler before it can run inside a SES Compartment.
const NEEDS_BUNDLING = { Dafny: true, Agda: true, Idris2: false };

function emoji(cls) {
  if (cls === 'pass') return '✅';
  if (cls === 'n/a' || cls === 'not-needed') return '—';
  return '❌';
}

function loadProblem(id) {
  return JSON.parse(fs.readFileSync(path.join(OUT_ROOT, id, 'results.json'), 'utf8'));
}

let BUNDLES = {};
try { BUNDLES = JSON.parse(fs.readFileSync(path.join(OUT_ROOT, 'bundles.json'), 'utf8')); }
catch (_) { BUNDLES = {}; }

function bundleFor(problemId, lang) {
  return (BUNDLES[problemId] || []).find((b) => b.tool === lang) || null;
}

function classifyBundle(b) {
  if (!b) return 'n/a';
  if (b.prepareError || b.bundleError) return 'bundle-failed';
  if (b.importError) return 'import-failed';
  if (b.sortError) return 'sort-failed';
  return 'pass';
}

function fmtNum(n) {
  return n.toLocaleString('en-US');
}

function trunc(s, max = 4000) {
  if (s.length <= max) return s;
  return s.slice(0, max) + `\n// ... truncated (${s.length - max} more bytes)`;
}

function renderProblem(p) {
  const lines = [];
  lines.push(`# ${p.problem.title}`);
  lines.push('');
  lines.push(p.problem.description);
  lines.push('');
  lines.push('## Summary');
  lines.push('');
  lines.push('| Language | Source LOC | Source bytes | Compiled bytes | Output | Status |');
  lines.push('| --- | ---: | ---: | ---: | --- | --- |');
  for (const r of p.results) {
    const out = r.run && r.run.stdout ? r.run.stdout.trim().replace(/\|/g, '\\|') : '(no output)';
    const status = r.passed ? '✅ ok' : '❌ fail';
    lines.push(`| ${r.language} | ${r.sourceLines} | ${fmtNum(r.sourceBytes)} | ${fmtNum(r.compiledBytes)} | \`${out}\` | ${status} |`);
  }
  lines.push('');
  lines.push('## SES compatibility');
  lines.push('');
  lines.push('| Language | Needs bundling | Static scan | `lockdown()` + `require()` | Raw `Compartment.evaluate()` | Bundled (`@endo/bundle-source` → `importBundle`) |');
  lines.push('| --- | :---: | :---: | :---: | :---: | :---: |');
  for (const r of p.results) {
    const ses = r.ses || {};
    const sf = (ses.staticFindings || []).map((s) => s.id).join(', ') || 'none';
    const lr = ses.lockdownRequire ? ses.lockdownRequire.classification : 'n/a';
    const ce = ses.compartmentEvaluate ? ses.compartmentEvaluate.classification : 'n/a';
    const needs = NEEDS_BUNDLING[r.language] ? '**yes**' : 'no';
    const bundle = bundleFor(p.problem.id, r.language);
    const bcls = classifyBundle(bundle);
    const sfMark = sf === 'none' ? '✅ clean' : `❌ ${sf}`;
    lines.push(`| ${r.language} | ${needs} | ${sfMark} | ${emoji(lr)} ${lr} | ${emoji(ce)} ${ce} | ${emoji(bcls)} ${bcls} |`);
  }
  lines.push('');
  // Per-cell bundle details
  const anyBundle = p.results.some((r) => bundleFor(p.problem.id, r.language));
  if (anyBundle) {
    lines.push('### Bundle details');
    lines.push('');
    lines.push('| Language | Bundle bytes (base64) | Imported keys | Notes |');
    lines.push('| --- | ---: | --- | --- |');
    for (const r of p.results) {
      const b = bundleFor(p.problem.id, r.language);
      if (!b) { lines.push(`| ${r.language} | — | — | not attempted |`); continue; }
      const note =
        b.prepareError ? `prepare error: \`${b.prepareError.slice(0, 120)}\`` :
        b.bundleError  ? `bundle error: \`${b.bundleError.slice(0, 120)}\`` :
        b.importError  ? `import error: \`${b.importError.slice(0, 120)}\`` :
        b.sortError    ? `sort-call error: \`${b.sortError.slice(0, 120)}\`` :
        b.sortMatches  ? `sort output matches expected` :
        b.importedKeys ? `imported keys: ${b.importedKeys.join(', ')}` :
        '';
      lines.push(`| ${r.language} | ${b.bundleBytes ? fmtNum(b.bundleBytes) : '—'} | ${b.importedKeys ? b.importedKeys.join(', ') : '—'} | ${note} |`);
    }
    lines.push('');
  }
  for (const r of p.results) {
    lines.push('---');
    lines.push('');
    lines.push(`## ${r.language}`);
    lines.push('');
    lines.push(`**Source** (\`${r.sourcePath}\`):`);
    lines.push('');
    lines.push('```' + LANG_FENCE[r.language]);
    lines.push(trunc(r.source, 10000));
    lines.push('```');
    lines.push('');
    lines.push(`**Build:** exit \`${r.build.exitCode}\``);
    if (r.build.stderr && r.build.stderr.trim()) {
      lines.push('');
      lines.push('<details><summary>build stderr</summary>');
      lines.push('');
      lines.push('```');
      lines.push(trunc(r.build.stderr, 1500));
      lines.push('```');
      lines.push('</details>');
    }
    lines.push('');
    if (r.run) {
      lines.push(`**Run:** exit \`${r.run.exitCode}\` — stdout: \`${(r.run.stdout || '').trim()}\``);
    }
    lines.push('');
    if (r.compiled) {
      for (const f of r.compiled) {
        lines.push(`**Generated JS** (\`${f.relPath}\`, ${fmtNum(f.bytes)} bytes):`);
        lines.push('');
        lines.push('```js');
        lines.push(trunc(f.content, 4000));
        lines.push('```');
        lines.push('');
      }
    }
    if (r.ses) {
      lines.push('**SES probes:**');
      lines.push('');
      const lr = r.ses.lockdownRequire;
      const ce = r.ses.compartmentEvaluate;
      lines.push(`- \`lockdown() + require()\`: **${lr.classification}** (exit ${lr.exitCode})`);
      if (lr.stderr && lr.stderr.trim()) {
        lines.push('  - stderr: `' + lr.stderr.trim().split('\n')[0].slice(0, 300) + '`');
      }
      lines.push(`- \`Compartment.evaluate()\`: **${ce.classification}** (exit ${ce.exitCode})`);
      if (ce.stderr && ce.stderr.trim()) {
        lines.push('  - stderr: `' + ce.stderr.trim().split('\n')[0].slice(0, 300) + '`');
      }
      lines.push('');
    }
  }
  return lines.join('\n');
}

function renderIndex(loaded) {
  const lines = [];
  lines.push('# Verified-Program JS Backend Comparison');
  lines.push('');
  lines.push('This directory holds an auto-generated, per-problem comparison of Dafny, Agda, and Idris2 JavaScript output, plus SES compatibility probes. See [EVALUATION.md](./EVALUATION.md) for the overall evaluation.');
  lines.push('');
  lines.push('## Problems');
  lines.push('');
  for (const p of loaded) {
    lines.push(`- [${p.problem.title}](./${p.problem.id}.md)`);
  }
  lines.push('');
  lines.push('## How to regenerate');
  lines.push('');
  lines.push('```');
  lines.push('nix develop  # or: have dafny, agda, idris2, nodejs on PATH');
  lines.push('npm install');
  lines.push('npm run all');
  lines.push('```');
  return lines.join('\n');
}

function renderEvaluation(loaded) {
  const lines = [];
  lines.push('# Evaluation: Dafny vs Agda vs Idris2 JavaScript backends');
  lines.push('');
  lines.push('Auto-generated summary of three dimensions:');
  lines.push('');
  lines.push('1. **Readability of the emitted JavaScript**');
  lines.push('2. **SES (Hardened JavaScript) compatibility**');
  lines.push('3. **Ease of interacting with objects from the outer JavaScript world**');
  lines.push('');
  lines.push('## Aggregate metrics');
  lines.push('');
  lines.push('| Problem | Lang | src LOC | compiled bytes | needs bundling | static scan | lockdown+require | raw compartment | bundled compartment |');
  lines.push('| --- | --- | ---: | ---: | :---: | :---: | :---: | :---: | :---: |');
  for (const p of loaded) {
    for (const r of p.results) {
      const ses = r.ses || {};
      const sf = (ses.staticFindings || []).map((s) => s.id).join(', ') || 'none';
      const lr = ses.lockdownRequire ? ses.lockdownRequire.classification : 'n/a';
      const ce = ses.compartmentEvaluate ? ses.compartmentEvaluate.classification : 'n/a';
      const needs = NEEDS_BUNDLING[r.language] ? '**yes**' : 'no';
      const b = bundleFor(p.problem.id, r.language);
      const bcls = classifyBundle(b);
      const sfMark = sf === 'none' ? '✅' : '❌';
      lines.push(`| ${p.problem.id} | ${r.language} | ${r.sourceLines} | ${fmtNum(r.compiledBytes)} | ${needs} | ${sfMark} | ${emoji(lr)} | ${emoji(ce)} | ${emoji(bcls)} |`);
    }
  }
  lines.push('');
  lines.push('Legend: ✅ pass, ❌ fail, — not applicable.');
  lines.push('');
  lines.push('See [hand-written notes](../EVALUATION.md) for the qualitative analysis (FFI ergonomics, readability commentary, etc.).');
  return lines.join('\n');
}

function main() {
  fs.mkdirSync(DOCS_ROOT, { recursive: true });
  const loaded = PROBLEMS.map((p) => loadProblem(p.id));
  for (const p of loaded) {
    fs.writeFileSync(path.join(DOCS_ROOT, `${p.problem.id}.md`), renderProblem(p));
  }
  fs.writeFileSync(path.join(DOCS_ROOT, 'README.md'), renderIndex(loaded));
  fs.writeFileSync(path.join(DOCS_ROOT, 'EVALUATION.md'), renderEvaluation(loaded));
  process.stderr.write(`Wrote ${loaded.length + 2} docs to ${path.relative(ROOT, DOCS_ROOT)}/\n`);
}

main();
