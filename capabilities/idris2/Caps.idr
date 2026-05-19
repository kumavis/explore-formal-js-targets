||| Two capability patterns in Idris2:
|||
||| 1. CONSUMING a host-provided capability — `validate` takes a Boolean
|||    predicate, but also calls a `%foreign`-bound JS function the host
|||    sets on `globalThis.__hostLog` before this program runs.
|||
||| 2. VENDING a capability — `makeCounter` builds a `Counter` record
|||    over a private `IORef`. The host can't reach the underlying ref
|||    except through the closed-over `bump` / `read` accessors, which
|||    is the same encapsulation discipline SES leans on.

module Main

import Data.IORef

-- The host-side logger lives at globalThis.__hostLog before this program
-- runs. %foreign wires the call straight through.
%foreign "javascript:lambda: (x) => globalThis.__hostLog(Number(x))"
prim__hostLog : Int -> PrimIO ()

hostLog : Int -> IO ()
hostLog n = primIO (prim__hostLog n)

-- Verified-shape validator that pipes each element through the host log
-- before testing it. The Idris2 type and control flow guarantee that
-- every visited element is logged regardless of the predicate's answer.
validate : (Int -> Bool) -> List Int -> IO Bool
validate _ [] = pure True
validate p (x :: xs) = do
  hostLog x
  if p x
    then validate p xs
    else pure False

-- A counter capability. The IORef is private to `makeCounter`; the
-- caller only ever sees the two thunks. Read/bump are the only paths
-- to the state.
record Counter where
  constructor MkCounter
  bump : IO Nat
  read : IO Nat

makeCounter : IO Counter
makeCounter = do
  ref <- newIORef Z
  let b : IO Nat
      b = do v <- readIORef ref
             let v' = S v
             writeIORef ref v'
             pure v'
  let r : IO Nat
      r = readIORef ref
  pure (MkCounter b r)

main : IO ()
main = do
  -- Direction 2: hold a vended counter and use it.
  c <- makeCounter
  a <- c.bump
  b <- c.bump
  d <- c.bump
  r <- c.read
  putStrLn ("[vend]    counter Bump x3 → " ++ show a ++ "," ++ show b ++ "," ++ show d
           ++ " ; Read = " ++ show r)

  -- Direction 1: consume host log via %foreign + JS predicate as Int -> Bool.
  ok1 <- validate (\x => x < 100) [10, 20, 30, 40]
  ok2 <- validate (\x => x < 30)  [10, 20, 30, 40]
  putStrLn ("[consume] validate (<100) [10,20,30,40] = " ++ show ok1)
  putStrLn ("[consume] validate (<30)  [10,20,30,40] = " ++ show ok2)
