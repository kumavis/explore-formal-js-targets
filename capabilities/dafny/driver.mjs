// Driver for the Dafny capability examples.
// Dafny emits a self-running script whose symbols live behind module-scoped
// `let` declarations (no module.exports), so we apply the same patch the
// bundle pipeline uses elsewhere in the repo: read the file, promote `let`s
// to globalThis, strip the launcher, then eval. Once that's done, we can
// pass JS-side capabilities to verified methods and call methods on the
// Dafny class instance the program vends back to us.

import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import BigNumber from 'bignumber.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
let src = fs.readFileSync(path.join(__dirname, 'Caps.js'), 'utf8');

// Strip the embedded Main invocation so loading is side-effect-free.
src = src.replace(/_dafny\.HandleHaltExceptions[\s\S]*$/, '');
// Promote the module-scoped `let X = …` to globals so we can reach them.
src = src.replace(/^let (_dafny|_System|Caps|_module) =/gm, 'globalThis.$1 =');

globalThis.BigNumber = BigNumber;
src = src.replace("require('bignumber.js')", 'globalThis.BigNumber');

eval(src);

// === DIRECTION 1: consume a host-supplied predicate ==========================
//
// ValidateAll has Dafny type `(int → bool, seq<int>) → bool`.  The first
// argument is a Dafny function value; at the JS calling convention it is
// just a JS function `(x) => boolean`.  Integers are BigNumber on the
// boundary, so we unwrap with .toNumber().
const hostPredicate = (x) => x.toNumber() % 2 === 0;
const xs = globalThis._dafny.Seq.of(
  new BigNumber(2), new BigNumber(4), new BigNumber(6), new BigNumber(8),
);
const ys = globalThis._dafny.Seq.of(
  new BigNumber(2), new BigNumber(3), new BigNumber(6), new BigNumber(8),
);
const allEvenXs = globalThis.Caps.__default.ValidateAll(hostPredicate, xs);
const allEvenYs = globalThis.Caps.__default.ValidateAll(hostPredicate, ys);
console.log('[consume]    ValidateAll(even, [2,4,6,8]) =', allEvenXs);
console.log('[consume]    ValidateAll(even, [2,3,6,8]) =', allEvenYs);

// === DIRECTION 2: hold the vended capability =================================
//
// `Counter` compiles to a JS class. `MakeCounter()` returns a fresh
// instance; the verified invariants ("count starts at 0", "Bump increases
// count by exactly 1", "Read observes the current count") apply at the
// machine level — there is no way for the host to break them without
// either editing the emitted file or replacing the class wholesale.
const counter = globalThis.Caps.__default.MakeCounter();
const a = counter.Bump();
const b = counter.Bump();
const c = counter.Bump();
const r = counter.Read();
console.log('[vend] Counter bump x3 → seen', a.toNumber(), b.toNumber(), c.toNumber(),
            '; Read =', r.toNumber());
