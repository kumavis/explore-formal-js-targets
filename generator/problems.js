'use strict';
const path = require('node:path');
const { extractDafny, extractAgda, extractIdris2 } = require('./extract.js');

// Each problem declares how its three implementations build, run, and
// what JS files we should consider its "compiled output" for inspection.
//
// All paths are relative to the project root.
//
// `runner` is invoked via { env, cwd, command, args }. It returns the
// child-process result; the harness captures stdout/stderr/exit code.

const ROOT = path.resolve(__dirname, '..');
const NODE_PATH_FOR_NPM = path.join(ROOT, 'node_modules');

function dafny(srcRel, expected) {
  const dir = path.join(ROOT, srcRel);
  const base = path.basename(srcRel.replace(/\/[^/]+$/, ''));
  // Dafny source: <Dir>.dfy → output <Dir>.js
  const src = require('node:fs').readdirSync(dir).find((f) => f.endsWith('.dfy'));
  if (!src) throw new Error(`no .dfy in ${dir}`);
  const stem = src.replace(/\.dfy$/, '');
  return {
    language: 'Dafny',
    sourcePath: path.join(dir, src),
    outputDir: dir,
    jsEntry: path.join(dir, `${stem}.js`),
    jsFiles: [`${stem}.js`],
    build: {
      command: 'nix',
      args: ['shell', 'nixpkgs#dafny', '--command', 'dafny', 'build', '--target:js', src],
      cwd: dir,
    },
    run: {
      command: 'node',
      args: [`${stem}.js`],
      cwd: dir,
      env: { NODE_PATH: NODE_PATH_FOR_NPM },
    },
    extractRelevant: (relPath, content) =>
      relPath === `${stem}.js` ? extractDafny(content, stem) : null,
    expected,
  };
}

function agda(srcRel, expected) {
  const dir = path.join(ROOT, srcRel);
  const src = require('node:fs').readdirSync(dir).find((f) => f.endsWith('.agda'));
  if (!src) throw new Error(`no .agda in ${dir}`);
  const stem = src.replace(/\.agda$/, '');
  return {
    language: 'Agda',
    sourcePath: path.join(dir, src),
    outputDir: dir,
    jsEntry: path.join(dir, `jAgda.${stem}.js`),
    // Resolved at build time: include the user module + agda-rts.js + every
    // jAgda.Agda.*.js stdlib module Agda emits alongside.
    jsFiles: (outDir) => require('node:fs').readdirSync(outDir).filter((f) => f.endsWith('.js')),
    build: {
      command: 'nix',
      args: ['shell', 'nixpkgs#agda', '--command', 'agda', '--js', '--js-optimize', '--compile-dir=.', src],
      cwd: dir,
    },
    run: {
      command: 'node',
      args: ['-e', `require('./jAgda.${stem}.js')`],
      cwd: dir,
      env: { NODE_PATH: dir },
    },
    extractRelevant: extractAgda,
    expected,
  };
}

function idris2(srcRel, execName, expected) {
  const dir = path.join(ROOT, srcRel);
  const src = require('node:fs').readdirSync(dir).find((f) => f.endsWith('.idr'));
  if (!src) throw new Error(`no .idr in ${dir}`);
  const stem = src.replace(/\.idr$/, '');
  return {
    language: 'Idris2',
    sourcePath: path.join(dir, src),
    outputDir: path.join(dir, 'build/exec'),
    jsEntry: path.join(dir, 'build/exec', execName),
    jsFiles: [execName],
    build: {
      command: 'sh',
      args: ['-c', `rm -rf build && nix shell nixpkgs#idris2 --command idris2 --cg node -o ${execName} ${src}`],
      cwd: dir,
    },
    run: {
      command: 'node',
      args: [path.join('build/exec', execName)],
      cwd: dir,
    },
    extractRelevant: (relPath, content) =>
      relPath === execName ? extractIdris2(content, stem) : null,
    expected,
  };
}

const PROBLEMS = [
  {
    id: 'factorial',
    title: 'Factorial (with positivity proof)',
    description:
      'Recursive factorial function with a proof that the result is at least 1. ' +
      'Dafny uses an SMT-discharged postcondition; Agda and Idris2 use an inductive ' +
      'predicate inhabited by a constructive term.',
    implementations: [
      dafny('problems/factorial/dafny', 'factorial(5) = 120'),
      agda('problems/factorial/agda', '120'),
      idris2('problems/factorial/idris2', 'factorial', '120'),
    ],
  },
  {
    id: 'reverse',
    title: 'List reverse (with reverse-reverse-identity proof)',
    description:
      'Naive list reverse with the theorem reverse(reverse(xs)) ≡ xs. ' +
      'Dafny proves it with SMT and a couple of induction lemmas; ' +
      'Agda and Idris2 prove it with structural induction and rewrite tactics.',
    implementations: [
      dafny('problems/reverse/dafny', 'reverse([1,2,3,4]) = [4, 3, 2, 1]'),
      agda('problems/reverse/agda', '[4,3,2,1]'),
      idris2('problems/reverse/idris2', 'reverse', '[4, 3, 2, 1]'),
    ],
  },
  {
    id: 'insertion-sort',
    title: 'Insertion sort (with sortedness proof)',
    description:
      'Insertion sort over a list of naturals. ' +
      'Dafny verifies both sortedness AND multiset-preservation (a true permutation proof). ' +
      'Agda and Idris2 verify sortedness via an inductive Sorted predicate and dependent ' +
      'transitivity lemmas.',
    implementations: [
      dafny('problems/insertion-sort/dafny', 'sort([3,1,4,1,5,9,2,6]) = [1, 1, 2, 3, 4, 5, 6, 9]'),
      agda('problems/insertion-sort/agda', '[1,1,2,3,4,5,6,9]'),
      idris2('problems/insertion-sort/idris2', 'insertionsort', '[1, 1, 2, 3, 4, 5, 6, 9]'),
    ],
  },
];

module.exports = { PROBLEMS, ROOT };
