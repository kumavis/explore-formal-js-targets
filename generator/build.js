#!/usr/bin/env node
'use strict';
// Compile each implementation, run it, capture stdout and the on-disk JS
// outputs. Persist a result manifest under outputs/<problem>/results.json
// that the report generator consumes.

const fs = require('node:fs');
const path = require('node:path');
const { spawnSync } = require('node:child_process');
const { PROBLEMS, ROOT } = require('./problems.js');

const OUT_ROOT = path.join(ROOT, 'outputs');

function run(step) {
  const env = { ...process.env, ...(step.env || {}) };
  const res = spawnSync(step.command, step.args, {
    cwd: step.cwd,
    env,
    encoding: 'utf8',
    maxBuffer: 64 * 1024 * 1024,
  });
  return {
    cmd: `${step.command} ${step.args.join(' ')}`,
    cwd: step.cwd,
    exitCode: res.status,
    stdout: res.stdout || '',
    stderr: res.stderr || '',
  };
}

function readCompiledJs(impl) {
  const out = [];
  for (const rel of impl.jsFiles) {
    const full = path.isAbsolute(rel) ? rel : path.join(impl.outputDir, rel);
    let content = '';
    let bytes = 0;
    try {
      content = fs.readFileSync(full, 'utf8');
      bytes = Buffer.byteLength(content);
    } catch (e) {
      content = `<unable to read: ${e.message}>`;
    }
    out.push({ relPath: rel, bytes, content });
  }
  return out;
}

function readSource(impl) {
  return fs.readFileSync(impl.sourcePath, 'utf8');
}

function main() {
  fs.mkdirSync(OUT_ROOT, { recursive: true });
  const manifest = [];
  for (const problem of PROBLEMS) {
    process.stderr.write(`\n=== ${problem.id} ===\n`);
    const probDir = path.join(OUT_ROOT, problem.id);
    fs.mkdirSync(probDir, { recursive: true });
    const results = [];
    for (const impl of problem.implementations) {
      process.stderr.write(`  [${impl.language}] building... `);
      const build = run(impl.build);
      process.stderr.write(`exit=${build.exitCode}\n`);
      let runRes = null;
      let compiled = null;
      if (build.exitCode === 0) {
        process.stderr.write(`  [${impl.language}] running...  `);
        runRes = run(impl.run);
        process.stderr.write(`exit=${runRes.exitCode}, stdout=${JSON.stringify(runRes.stdout.trim().slice(0, 60))}\n`);
        compiled = readCompiledJs(impl);
      }
      const source = readSource(impl);
      const totalBytes = compiled ? compiled.reduce((a, b) => a + b.bytes, 0) : 0;
      results.push({
        language: impl.language,
        sourcePath: path.relative(ROOT, impl.sourcePath),
        sourceLines: source.split('\n').length,
        sourceBytes: Buffer.byteLength(source),
        source,
        compiled,
        compiledBytes: totalBytes,
        build,
        run: runRes,
        expected: impl.expected,
        passed:
          runRes &&
          runRes.exitCode === 0 &&
          runRes.stdout.trim().includes(impl.expected),
      });
    }
    const out = { problem, results };
    fs.writeFileSync(
      path.join(probDir, 'results.json'),
      JSON.stringify(out, null, 2),
    );
    manifest.push({ id: problem.id, title: problem.title });
  }
  fs.writeFileSync(
    path.join(OUT_ROOT, 'manifest.json'),
    JSON.stringify(manifest, null, 2),
  );
  process.stderr.write('\nDone.\n');
}

main();
