-- Dynamic sealer / unsealer pair, after agoric-labs/jesc24's `sealing.v`.
--
-- Agda has no native heap or weak maps, so the sealer is a `postulate`
-- bound to a JS-side implementation via `{-# COMPILE JS #-}`. The
-- *Agda type* expresses the contract:
--
--    makeSealer : IO Sealer
--    seal       : Sealer -> Nat -> IO Token
--    unseal     : Sealer -> Token -> IO (Maybe Nat)
--
-- Token is an opaque Set; only the JS side knows it's actually a
-- closure-keyed reference. The privacy comes from the JS closure, not
-- from Agda — but the Agda type checker rules out, e.g., calling
-- `unseal s (suc zero)` or other "made up" tokens of the wrong shape.

module Sealer where

open import Agda.Builtin.Nat
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

-- Minimal IO plumbing (Agda.Builtin.IO is just the type).
infixl 1 _>>=_
postulate
  return : {A : Set} -> A -> IO A
  _>>=_  : {A B : Set} -> IO A -> (A -> IO B) -> IO B
{-# COMPILE JS return = (_) => (x) => (cb) => cb(x) #-}
{-# COMPILE JS _>>=_  = (_) => (_) => (m) => (k) => (cb) => m((v) => k(v)(cb)) #-}

postulate
  putStrLn   : String -> IO ⊤
  natToStr   : Nat    -> String
{-# COMPILE JS putStrLn  = (s) => (cb) => { process.stdout.write(s + "\n"); cb({}); } #-}
{-# COMPILE JS natToStr  = (n) => n.toString() #-}

infixr 5 _++_
_++_ : String -> String -> String
s ++ t = primStringAppend s t

-- The sealer interface.
postulate
  Sealer      : Set
  Token       : Set
  Maybe       : Set -> Set
  nothing     : {A : Set} -> Maybe A
  just        : {A : Set} -> A -> Maybe A
  makeSealer  : IO Sealer
  seal        : Sealer -> Nat   -> IO Token
  unseal      : Sealer -> Token -> IO (Maybe Nat)
  showMaybe   : Maybe Nat -> String

{-# COMPILE JS Sealer    = null #-}
{-# COMPILE JS Token     = null #-}
{-# COMPILE JS Maybe     = (_) => null #-}
{-# COMPILE JS nothing   = (_) => ({ tag: 0 }) #-}
{-# COMPILE JS just      = (_) => (x) => ({ tag: 1, val: x }) #-}
{-# COMPILE JS makeSealer = (cb) => {
  const tbl = new WeakMap();
  cb({
    seal:   (v) => { const k = Object.freeze({}); tbl.set(k, v); return k; },
    unseal: (k) => tbl.has(k) ? { tag: 1, val: tbl.get(k) } : { tag: 0 }
  });
} #-}
{-# COMPILE JS seal      = (s) => (v) => (cb) => cb(s.seal(v)) #-}
{-# COMPILE JS unseal    = (s) => (k) => (cb) => cb(s.unseal(k)) #-}
{-# COMPILE JS showMaybe = (m) => m.tag === 0 ? "nothing" : ("just " + m.val.toString()) #-}

main : IO ⊤
main =
  makeSealer       >>= \ s1 ->
  makeSealer       >>= \ s2 ->
  seal s1 42       >>= \ k  ->
  unseal s1 k      >>= \ r1 ->
  putStrLn ("s1.unseal(s1.seal(42)) = " ++ showMaybe r1) >>= \ _ ->
  unseal s2 k      >>= \ r2 ->
  putStrLn ("s2.unseal(s1.seal(42)) = " ++ showMaybe r2)
