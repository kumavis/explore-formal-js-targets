#!/usr/bin/env node
'use strict';
// Probe how easy it is to call each compiler's verified `sort` function
// with a JS-supplied array of numbers and to read the result back.
// We try Dafny → Agda → Idris2 and write a one-line verdict per tool.

const fs = require('node:fs');
const path = require('node:path');
const { spawnSync } = require('node:child_process');
const { ROOT } = require('./problems.js');

const NODE_PATH_FOR_NPM = path.join(ROOT, 'node_modules');

function run(cwd, source, env = {}) {
  const res = spawnSync(process.execPath, ['-e', source], {
    cwd,
    env: { ...process.env, ...env },
    encoding: 'utf8',
    maxBuffer: 16 * 1024 * 1024,
    timeout: 15000,
  });
  return {
    exitCode: res.status,
    stdout: (res.stdout || '').trim(),
    stderr: (res.stderr || '').trim(),
  };
}

const probes = [];

// === Dafny ===
// The output file uses module-scoped `let _dafny = …` and
// `let InsertionSort = …`, then at the bottom invokes Main. There's no
// `module.exports` and the top-level lets are unreachable from outside.
// To call Sort from JS we patch the source: rewrite the top-level `let`s
// to `globalThis.X =` and strip the trailing Main-invocation, then eval.
{
  const dir = path.join(ROOT, 'problems/insertion-sort/dafny');
  const driver = `
    const fs = require('fs');
    const BigNumber = require('bignumber.js');
    let src = fs.readFileSync('./InsertionSort.js', 'utf8');
    // Strip the trailing Main invocation.
    src = src.replace(/_dafny\\.HandleHaltExceptions[\\s\\S]*$/, '');
    // Promote module-scoped lets to globalThis so we can reach them.
    src = src.replace(/^let _dafny =/m,        'globalThis._dafny =');
    src = src.replace(/^let _System =/m,       'globalThis._System =');
    src = src.replace(/^let InsertionSort =/m, 'globalThis.InsertionSort =');
    src = src.replace(/^let _module =/m,       'globalThis._module =');
    // bignumber.js is required from the file; satisfy it manually.
    globalThis.BigNumber = BigNumber;
    src = src.replace("require('bignumber.js')", 'globalThis.BigNumber');
    eval(src);
    const inSeq = globalThis._dafny.Seq.of(new BigNumber(7), new BigNumber(3), new BigNumber(5), new BigNumber(1), new BigNumber(9), new BigNumber(2));
    const outSeq = globalThis.InsertionSort.__default.Sort(inSeq);
    const outArr = [];
    for (let i = 0; i < outSeq.length; i++) outArr.push(outSeq[i].toNumber());
    console.log(JSON.stringify(outArr));
  `;
  const r = run(dir, driver, { NODE_PATH: NODE_PATH_FOR_NPM });
  probes.push({ tool: 'Dafny', ok: r.exitCode === 0, stdout: r.stdout, stderr: r.stderr.slice(0, 300) });
}

// === Agda ===
// Each top-level Agda def becomes a curried JS function on `exports`.
// `sort` is `exports["sort"]`, and lists are flat JS arrays under
// --js-optimize. Numbers must be BigInts because Nat is represented as
// BigInt by the runtime.
{
  const dir = path.join(ROOT, 'problems/insertion-sort/agda');
  const driver = `
    const m = require('./jAgda.InsertionSort.js');
    const input = [7n, 3n, 5n, 1n, 9n, 2n];
    const out = m.sort(input);
    console.log(JSON.stringify(out.map(b => Number(b))));
  `;
  const r = run(dir, driver, { NODE_PATH: dir });
  probes.push({ tool: 'Agda', ok: r.exitCode === 0, stdout: r.stdout, stderr: r.stderr.slice(0, 300) });
}

// === Idris2 ===
// The Node backend produces a self-contained #!/usr/bin/env node executable
// whose top is a long IIFE-like script that ends with try{__mainExpression_0()}.
// There's no clean module surface; calling `sort` from outside means either
//   (a) reading the file as text, stripping the trailing main invocation,
//       and evaluating it in a Function() scope to grab the symbol, or
//   (b) recompiling with %export bindings (not a node-cg feature today).
// We do (a) as a worst-case experiment.
{
  const dir = path.join(ROOT, 'problems/insertion-sort/idris2/build/exec');
  const driver = `
    const fs = require('fs');
    let src = fs.readFileSync('./insertionsort', 'utf8');
    // Drop the shebang and trailing main-invocation line.
    src = src.replace(/^#![^\\n]*\\n/, '');
    src = src.replace(/\\ntry\\{__mainExpression_0[\\s\\S]*$/, '');
    // Find the demangled sort: Idris2 mangles per the module; locate the symbol.
    const m = src.match(/(InsertionSort_[a-zA-Z0-9_]*sort[a-zA-Z0-9_]*)/);
    if (!m) throw new Error('no sort symbol found');
    const symbol = m[1];
    src += '\\nreturn ' + symbol + ';';
    const sortFn = new Function(src)();
    // Idris2 list rep: { a1: head, a2: tail } / { h: 0 } for nil.
    function toIdrisList(arr) {
      let acc = { h: 0 };
      for (let i = arr.length - 1; i >= 0; i--) acc = { a1: BigInt(arr[i]), a2: acc };
      return acc;
    }
    function fromIdrisList(x) {
      const out = [];
      while (x.h === undefined) { out.push(Number(x.a1)); x = x.a2; }
      return out;
    }
    const result = sortFn(toIdrisList([7, 3, 5, 1, 9, 2]));
    console.log(JSON.stringify(fromIdrisList(result)));
  `;
  const r = run(dir, driver);
  probes.push({ tool: 'Idris2', ok: r.exitCode === 0, stdout: r.stdout, stderr: r.stderr.slice(0, 300) });
}

fs.mkdirSync(path.join(ROOT, 'outputs'), { recursive: true });
fs.writeFileSync(path.join(ROOT, 'outputs', 'ffi-probe.json'), JSON.stringify(probes, null, 2));

for (const p of probes) {
  process.stdout.write(`${p.tool.padEnd(8)} ${p.ok ? 'PASS' : 'FAIL'}  ${p.stdout || p.stderr}\n`);
}
