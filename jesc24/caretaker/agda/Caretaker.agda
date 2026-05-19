-- Revocable caretaker, after agoric-labs/jesc24's
-- `theories/heap_lang/lib/caretaker.v`.
--
-- Agda is pure; the caretaker's enabled-flag lives in a JS closure and
-- is reached through `postulate + {-# COMPILE JS #-}`. The Agda type
-- expresses the contract; the privacy comes from the JS closure.

module Caretaker where

open import Agda.Builtin.Nat
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

-- Minimal IO plumbing.
infixl 1 _>>=_
postulate
  return : {A : Set} -> A -> IO A
  _>>=_  : {A B : Set} -> IO A -> (A -> IO B) -> IO B
{-# COMPILE JS return = (_) => (x) => (cb) => cb(x) #-}
{-# COMPILE JS _>>=_  = (_) => (_) => (m) => (k) => (cb) => m((v) => k(v)(cb)) #-}

postulate
  putStrLn : String -> IO ⊤
  natToStr : Nat    -> String
{-# COMPILE JS putStrLn = (s) => (cb) => { process.stdout.write(s + "\n"); cb({}); } #-}
{-# COMPILE JS natToStr = (n) => n.toString() #-}

infixr 5 _++_
_++_ : String -> String -> String
s ++ t = primStringAppend s t

-- The caretaker interface.
postulate
  Caretaker      : Set
  Maybe          : Set -> Set
  nothing        : {A : Set} -> Maybe A
  just           : {A : Set} -> A -> Maybe A
  makeCaretaker  : (Nat -> Nat) -> IO Caretaker
  wrap           : Caretaker -> Nat -> IO (Maybe Nat)
  enable         : Caretaker -> IO ⊤
  disable        : Caretaker -> IO ⊤
  showMaybe      : Maybe Nat -> String

{-# COMPILE JS Caretaker     = null #-}
{-# COMPILE JS Maybe         = (_) => null #-}
{-# COMPILE JS nothing       = (_) => ({ tag: 0 }) #-}
{-# COMPILE JS just          = (_) => (x) => ({ tag: 1, val: x }) #-}
{-# COMPILE JS makeCaretaker = (f) => (cb) => {
  let on = false;
  cb({
    wrap:    (v) => on ? { tag: 1, val: f(v) } : { tag: 0 },
    enable:  () => { on = true; },
    disable: () => { on = false; }
  });
} #-}
{-# COMPILE JS wrap     = (c) => (v) => (cb) => cb(c.wrap(v)) #-}
{-# COMPILE JS enable   = (c) => (cb) => { c.enable();  cb({}); } #-}
{-# COMPILE JS disable  = (c) => (cb) => { c.disable(); cb({}); } #-}
{-# COMPILE JS showMaybe = (m) => m.tag === 0 ? "nothing" : ("just " + m.val.toString()) #-}

double : Nat -> Nat
double n = n + n

main : IO ⊤
main =
  makeCaretaker double >>= \ c ->
  -- default disabled
  wrap c 10            >>= \ r0 ->
  putStrLn ("default (disabled): wrap 10 = " ++ showMaybe r0) >>= \ _ ->
  enable c             >>= \ _ ->
  wrap c 10            >>= \ r1 ->
  putStrLn ("enabled:            wrap 10 = " ++ showMaybe r1) >>= \ _ ->
  wrap c 7             >>= \ r2 ->
  putStrLn ("enabled:            wrap 7  = " ++ showMaybe r2) >>= \ _ ->
  disable c            >>= \ _ ->
  wrap c 10            >>= \ r3 ->
  putStrLn ("disabled:           wrap 10 = " ++ showMaybe r3)
