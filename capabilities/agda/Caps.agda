-- Two capability patterns in Agda.
--
-- Agda is pure: there's no built-in IORef, no `do` over arbitrary monads
-- without setting up the binding combinator yourself, and no built-in
-- machinery for stateful objects. Both directions therefore go through
-- `postulate ... {-# COMPILE JS … #-}` — the same FFI escape hatch we
-- use for `putStrLn` elsewhere in the repo.

module Caps where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

-- --- Minimal IO plumbing ---------------------------------------------------
--
-- Agda.Builtin.IO only declares the *type* `IO : Set -> Set`. The bind
-- operator is on us; we wire it through %foreign-style pragmas.

infixl 1 _>>=_
postulate
  return : {A : Set} -> A -> IO A
  _>>=_  : {A B : Set} -> IO A -> (A -> IO B) -> IO B
{-# COMPILE JS return = (_) => (x) => (cb) => cb(x) #-}
{-# COMPILE JS _>>=_  = (_) => (_) => (m) => (k) => (cb) => m((v) => k(v)(cb)) #-}

-- A few stringification + I/O atoms we'll need to print results.
postulate
  putStrLn   : String -> IO ⊤
  hostLog    : Nat    -> IO ⊤
  natToStr   : Nat    -> String
  boolToStr  : Bool   -> String
{-# COMPILE JS putStrLn  = (s) => (cb) => { process.stdout.write(s + "\n"); cb({}); } #-}
{-# COMPILE JS hostLog   = (n) => (cb) => { globalThis.__hostLog(Number(n)); cb({}); } #-}
{-# COMPILE JS natToStr  = (n) => n.toString() #-}
{-# COMPILE JS boolToStr = (b) => b ? "true" : "false" #-}

infixr 5 _++_
_++_ : String -> String -> String
s ++ t = primStringAppend s t

-- --- Direction 1: CONSUME a host capability --------------------------------
--
-- `validate` walks a list, logs every element via the host's `hostLog`
-- (set on globalThis by the driver), and checks each against a predicate.

-- `if_then_else_` isn't in Agda.Builtin.Bool; pattern-match instead.
validate : (Nat -> Bool) -> List Nat -> IO Bool
validate _ []       = return true
validate p (x ∷ xs) = hostLog x >>= \_ -> aux (p x)
  where
    aux : Bool -> IO Bool
    aux true  = validate p xs
    aux false = return false

-- --- Direction 2: VEND a capability ----------------------------------------
--
-- Agda has no native mutable state. We FFI-bind a JS object whose
-- `bump` / `read` methods close over a private counter, and surface it as
-- an opaque `Counter` type. The Agda layer can ONLY use it via the typed
-- `bumpC` / `readC` calls; the actual closure cell isn't reachable.

postulate
  Counter     : Set
  makeCounter : IO Counter
  bumpC       : Counter -> IO Nat
  readC       : Counter -> IO Nat
{-# COMPILE JS Counter     = null #-}
{-# COMPILE JS makeCounter = (cb) => { let n = 0n; cb({ bump: () => ++n, read: () => n }); } #-}
{-# COMPILE JS bumpC       = (c) => (cb) => cb(c.bump()) #-}
{-# COMPILE JS readC       = (c) => (cb) => cb(c.read()) #-}

-- --- Demo -------------------------------------------------------------------

main : IO ⊤
main =
  makeCounter                                        >>= \c ->
  bumpC c                                            >>= \a ->
  bumpC c                                            >>= \b ->
  bumpC c                                            >>= \d ->
  readC c                                            >>= \r ->
  putStrLn ("[vend]    counter Bump x3 → "
            ++ natToStr a ++ "," ++ natToStr b ++ "," ++ natToStr d
            ++ " ; Read = " ++ natToStr r)           >>= \_ ->
  validate (\x -> x < 100) (10 ∷ 20 ∷ 30 ∷ 40 ∷ []) >>= \ok1 ->
  putStrLn ("[consume] validate (<100) [10,20,30,40] = " ++ boolToStr ok1) >>= \_ ->
  validate (\x -> x < 30)  (10 ∷ 20 ∷ 30 ∷ 40 ∷ []) >>= \ok2 ->
  putStrLn ("[consume] validate (<30)  [10,20,30,40] = " ++ boolToStr ok2)
