#!/usr/bin/env node
// Bundle each implementation's emitted JavaScript with @endo/bundle-source,
// then load the bundle into a SES Compartment via @endo/import-bundle.
// For insertion-sort we additionally invoke the verified `sort` function
// and check the output. Results land in outputs/<problem>/bundle.json.
//
// Pre-processing pass per tool (none emit a clean library surface by default):
//
//   - Dafny:  strip the trailing Main invocation, expose the module-scoped
//             `let`s on module.exports, declare bignumber.js as a real
//             bundled dependency (copy it into the bundle's node_modules).
//   - Agda:   collect all sibling jAgda.<Mod>.js + agda-rts.js into one dir,
//             rewrite bare-specifier requires to relative requires, strip
//             the trailing exports.main(...) side effect from the entry.
//   - Idris2: strip the shebang and the trailing __mainExpression_0()
//             invocation, expose the mangled target symbol on module.exports.

import '@endo/init';
import bundleSource from '@endo/bundle-source';
import { importBundle } from '@endo/import-bundle';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const ROOT = path.resolve(path.dirname(__filename), '..');
const OUT_ROOT = path.join(ROOT, 'outputs');
const BUNDLES_ROOT = path.join(OUT_ROOT, 'bundles');

const SORT_INPUT_INT = [7, 3, 5, 1, 9, 2];
const SORT_EXPECTED  = [1, 2, 3, 5, 7, 9];

// === Pre-processors ============================================================

function prepareDafny(srcDir, destDir) {
  fs.rmSync(destDir, { recursive: true, force: true });
  fs.mkdirSync(destDir, { recursive: true });
  const srcFile = fs.readdirSync(srcDir).find((f) => f.endsWith('.js'));
  let content = fs.readFileSync(path.join(srcDir, srcFile), 'utf8');
  content = content.replace(/_dafny\.HandleHaltExceptions[\s\S]*$/, '');
  const letMatches = [...content.matchAll(/^let (\w+) = \(function\(\) \{/gm)];
  const exports = letMatches.map((m) => m[1]);
  content += `\nmodule.exports = { ${exports.join(', ')} };\n`;
  fs.writeFileSync(path.join(destDir, srcFile), content);
  fs.writeFileSync(path.join(destDir, 'package.json'), JSON.stringify({
    name: 'dafny-bundle', type: 'commonjs', main: srcFile,
    dependencies: { 'bignumber.js': '*' },
  }, null, 2));
  // Copy bignumber.js into the bundle's node_modules (compartment-mapper
  // doesn't follow symlinks).
  const dst = path.join(destDir, 'node_modules', 'bignumber.js');
  fs.mkdirSync(dst, { recursive: true });
  const src = path.join(ROOT, 'node_modules', 'bignumber.js');
  for (const f of fs.readdirSync(src)) fs.cpSync(path.join(src, f), path.join(dst, f), { recursive: true });
  return { entry: path.join(destDir, srcFile), exports };
}

function prepareAgda(srcDir, destDir) {
  fs.rmSync(destDir, { recursive: true, force: true });
  fs.mkdirSync(destDir, { recursive: true });
  const allJs = fs.readdirSync(srcDir).filter((f) => f.endsWith('.js'));
  let entryFile = null;
  for (const f of allJs) {
    let content = fs.readFileSync(path.join(srcDir, f), 'utf8');
    content = content.replace(/require\(["']agda-rts["']\)/g, 'require("./agda-rts.js")');
    content = content.replace(/require\(["'](jAgda\.[^"']+)["']\)/g, 'require("./$1.js")');
    if (!f.startsWith('jAgda.Agda.')) {
      content = content.replace(/\nexports\["main"\]\(a => \(\{\}\)\)\s*$/, '\n');
      entryFile = f;
    }
    fs.writeFileSync(path.join(destDir, f), content);
  }
  if (!entryFile) throw new Error(`no jAgda entry in ${srcDir}`);
  fs.writeFileSync(path.join(destDir, 'package.json'), JSON.stringify({
    name: 'agda-bundle', type: 'commonjs', main: entryFile,
  }, null, 2));
  return { entry: path.join(destDir, entryFile) };
}

function prepareIdris2(execPath, destDir, targetSymbolRegex, asName) {
  fs.rmSync(destDir, { recursive: true, force: true });
  fs.mkdirSync(destDir, { recursive: true });
  let content = fs.readFileSync(execPath, 'utf8');
  content = content.replace(/^#![^\n]*\n/, '');
  content = content.replace(/\ntry\{__mainExpression_0[\s\S]*$/, '');
  const m = content.match(targetSymbolRegex);
  if (!m) throw new Error(`no symbol matching ${targetSymbolRegex} in ${execPath}`);
  const symbol = m[1];
  content += `\nmodule.exports = { ${asName}: ${symbol} };\n`;
  const out = path.join(destDir, 'entry.js');
  fs.writeFileSync(out, content);
  fs.writeFileSync(path.join(destDir, 'package.json'), JSON.stringify({
    name: 'idris2-bundle', type: 'commonjs', main: 'entry.js',
  }, null, 2));
  return { entry: out, symbol };
}

// === Sort adapters (only used for insertion-sort) ==========================

const ADAPTERS = {
  Dafny: (BigNumber) => ({
    toIn(arr) { return globalThis.__bundle_ns._dafny.Seq.of(...arr.map((n) => new BigNumber(n))); },
    fromOut(seq) { const out = []; for (let i = 0; i < seq.length; i++) out.push(seq[i].toNumber()); return out; },
    call(ns, input) { return ns.InsertionSort.__default.Sort(input); },
  }),
  Agda: () => ({
    toIn(arr) { return arr.map((n) => BigInt(n)); },
    fromOut(arr) { return arr.map((b) => Number(b)); },
    call(ns, input) { return ns.sort(input); },
  }),
  Idris2: () => ({
    toIn(arr) {
      let acc = { h: 0 };
      for (let i = arr.length - 1; i >= 0; i--) acc = { a1: BigInt(arr[i]), a2: acc };
      return acc;
    },
    fromOut(node) {
      const out = [];
      while (node.h === undefined) { out.push(Number(node.a1)); node = node.a2; }
      return out;
    },
    call(ns, input) { return ns.sort(input); },
  }),
};

// === Bundle + import one impl ===============================================

async function bundleAndImport(tool, prepared, opts = {}) {
  const r = {
    tool,
    bundleBytes: 0,
    bundleFormat: null,
    bundleError: null,
    importError: null,
    importedKeys: null,
  };
  let bundle;
  try {
    bundle = await bundleSource(prepared.entry);
    r.bundleFormat = bundle.moduleFormat;
    r.bundleBytes = bundle.endoZipBase64?.length || 0;
  } catch (e) {
    r.bundleError = (e && e.message) || String(e);
    return { r, ns: null };
  }
  try {
    const ns = await importBundle(bundle, { endowments: opts.endowments || { console } });
    r.importedKeys = Object.keys(ns);
    return { r, ns };
  } catch (e) {
    r.importError = (e && e.message) || String(e);
    return { r, ns: null };
  }
}

// === Driver =================================================================

const BigNumber = (await import('bignumber.js')).default;

const TASKS = [
  {
    problem: 'factorial',
    impls: [
      { tool: 'Dafny', kind: 'dafny', prep: () => prepareDafny(
          path.join(ROOT, 'problems/factorial/dafny'),
          path.join(BUNDLES_ROOT, 'factorial/dafny')) },
      { tool: 'Agda',  kind: 'agda',  prep: () => prepareAgda(
          path.join(ROOT, 'problems/factorial/agda'),
          path.join(BUNDLES_ROOT, 'factorial/agda')) },
      { tool: 'Idris2', kind: 'idris2', prep: () => prepareIdris2(
          path.join(ROOT, 'problems/factorial/idris2/build/exec/factorial'),
          path.join(BUNDLES_ROOT, 'factorial/idris2'),
          /\b([A-Z]\w*_factorial)\b/, 'factorial') },
    ],
  },
  {
    problem: 'reverse',
    impls: [
      { tool: 'Dafny', kind: 'dafny', prep: () => prepareDafny(
          path.join(ROOT, 'problems/reverse/dafny'),
          path.join(BUNDLES_ROOT, 'reverse/dafny')) },
      { tool: 'Agda',  kind: 'agda',  prep: () => prepareAgda(
          path.join(ROOT, 'problems/reverse/agda'),
          path.join(BUNDLES_ROOT, 'reverse/agda')) },
      { tool: 'Idris2', kind: 'idris2', prep: () => prepareIdris2(
          path.join(ROOT, 'problems/reverse/idris2/build/exec/reverse'),
          path.join(BUNDLES_ROOT, 'reverse/idris2'),
          /\b([A-Z]\w*_myReverse)\b/, 'reverse') },
    ],
  },
  {
    problem: 'insertion-sort',
    runSort: true,
    impls: [
      { tool: 'Dafny', kind: 'dafny', prep: () => prepareDafny(
          path.join(ROOT, 'problems/insertion-sort/dafny'),
          path.join(BUNDLES_ROOT, 'insertion-sort/dafny')) },
      { tool: 'Agda',  kind: 'agda',  prep: () => prepareAgda(
          path.join(ROOT, 'problems/insertion-sort/agda'),
          path.join(BUNDLES_ROOT, 'insertion-sort/agda')) },
      { tool: 'Idris2', kind: 'idris2', prep: () => prepareIdris2(
          path.join(ROOT, 'problems/insertion-sort/idris2/build/exec/insertionsort'),
          path.join(BUNDLES_ROOT, 'insertion-sort/idris2'),
          /\b([A-Z]\w*_sort)\b/, 'sort') },
    ],
  },
  {
    problem: 'vec-zipwith',
    impls: [
      { tool: 'Dafny', kind: 'dafny', prep: () => prepareDafny(
          path.join(ROOT, 'problems/vec-zipwith/dafny'),
          path.join(BUNDLES_ROOT, 'vec-zipwith/dafny')) },
      { tool: 'Agda',  kind: 'agda',  prep: () => prepareAgda(
          path.join(ROOT, 'problems/vec-zipwith/agda'),
          path.join(BUNDLES_ROOT, 'vec-zipwith/agda')) },
      { tool: 'Idris2', kind: 'idris2', prep: () => prepareIdris2(
          path.join(ROOT, 'problems/vec-zipwith/idris2/build/exec/veczipwith'),
          path.join(BUNDLES_ROOT, 'vec-zipwith/idris2'),
          /\b([A-Z]\w*_zipWith)\b/, 'zipWith') },
    ],
  },
  {
    problem: 'sum-formula',
    impls: [
      { tool: 'Dafny', kind: 'dafny', prep: () => prepareDafny(
          path.join(ROOT, 'problems/sum-formula/dafny'),
          path.join(BUNDLES_ROOT, 'sum-formula/dafny')) },
      { tool: 'Agda',  kind: 'agda',  prep: () => prepareAgda(
          path.join(ROOT, 'problems/sum-formula/agda'),
          path.join(BUNDLES_ROOT, 'sum-formula/agda')) },
      { tool: 'Idris2', kind: 'idris2', prep: () => prepareIdris2(
          path.join(ROOT, 'problems/sum-formula/idris2/build/exec/sumformula'),
          path.join(BUNDLES_ROOT, 'sum-formula/idris2'),
          /\b([A-Z]\w*_sum)\b/, 'sum') },
    ],
  },
];

const all = {};
for (const t of TASKS) {
  process.stderr.write(`\n=== bundling ${t.problem} ===\n`);
  all[t.problem] = [];
  for (const impl of t.impls) {
    process.stderr.write(`  [${impl.tool}] prep+bundle+import... `);
    let prepared;
    try { prepared = impl.prep(); }
    catch (e) {
      process.stderr.write(`PREP-FAIL (${e.message})\n`);
      all[t.problem].push({ tool: impl.tool, prepareError: e.message });
      continue;
    }
    // Dafny pulls bignumber.js, which calls Math.random() during init —
    // SES's secure-mode Math removes random(). Endowing the host Math is
    // the documented escape hatch. (Real deployments should wrap Math.)
    const endowments = impl.kind === 'dafny'
      ? { console, BigNumber, Math }
      : { console };
    const { r, ns } = await bundleAndImport(impl.tool, prepared, { endowments });
    r.endowments = Object.keys(endowments);
    if (t.runSort && ns) {
      try {
        const adapter = ADAPTERS[impl.tool](BigNumber);
        if (impl.kind === 'dafny') globalThis.__bundle_ns = ns;
        const out = adapter.call(ns, adapter.toIn(SORT_INPUT_INT));
        const arr = adapter.fromOut(out);
        r.sortOutput = arr;
        r.sortMatches = JSON.stringify(arr) === JSON.stringify(SORT_EXPECTED);
      } catch (e) {
        r.sortError = (e && e.message) || String(e);
      }
    }
    if (r.bundleError) process.stderr.write(`BUNDLE-FAIL ${r.bundleError.slice(0,80)}\n`);
    else if (r.importError) process.stderr.write(`IMPORT-FAIL ${r.importError.slice(0,80)}\n`);
    else if (t.runSort) {
      process.stderr.write(
        r.sortMatches ? `ok (sort=${JSON.stringify(r.sortOutput)})\n` :
        r.sortError    ? `SORT-FAIL ${r.sortError.slice(0,80)}\n`     :
                         `ok (no sort check)\n`,
      );
    } else {
      process.stderr.write(`ok (imported: ${r.importedKeys.length} keys)\n`);
    }
    all[t.problem].push(r);
  }
}

fs.mkdirSync(OUT_ROOT, { recursive: true });
fs.writeFileSync(path.join(OUT_ROOT, 'bundles.json'), JSON.stringify(all, null, 2));
process.stderr.write(`\nWrote outputs/bundles.json\n`);
