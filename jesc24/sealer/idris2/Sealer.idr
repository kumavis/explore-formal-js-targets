||| Dynamic sealer / unsealer pair, after agoric-labs/jesc24's
||| `sealing.v` (simpler direct version).
|||
||| A *sealer* takes a value and returns an opaque token; the matching
||| *unsealer* takes a token and either returns the originally sealed
||| value or — if the token wasn't issued by this sealer — `Nothing`.
||| Cross-sealer tokens are not unsealable: that's the OCAP property.
|||
||| The implementation closes a private `IORef` over a counter + a
||| list of (id, value) pairs. The token's internal `Nat` is only
||| meaningful inside the closure of that sealer instance.

module Main

import Data.IORef
import Data.List

-- An opaque token. The constructor is local to this module; outside
-- callers can only get a Token by calling `seal`.
data Token : Type where
  MkToken : Nat -> Token

Show Token where
  show (MkToken n) = "token#" ++ show n

record Sealer where
  constructor MkSealer
  seal   : Nat   -> IO Token
  unseal : Token -> IO (Maybe Nat)

makeSealer : IO Sealer
makeSealer = do
  -- State: (next-id, list of (id, value)).
  st <- newIORef (the (Nat, List (Nat, Nat)) (Z, []))
  let sealOp : Nat -> IO Token
      sealOp v = do
        (n, tbl) <- readIORef st
        writeIORef st (S n, (n, v) :: tbl)
        pure (MkToken n)
  let unsealOp : Token -> IO (Maybe Nat)
      unsealOp (MkToken id) = do
        (_, tbl) <- readIORef st
        pure (lookup id tbl)
  pure (MkSealer sealOp unsealOp)

main : IO ()
main = do
  s1 <- makeSealer
  s2 <- makeSealer

  -- Round-trip: s1.unseal . s1.seal = id (up to Just)
  k <- s1.seal 42
  r1 <- s1.unseal k
  putStrLn ("s1.unseal(s1.seal(42)) = " ++ show r1)

  -- Cross-sealer: s2.unseal of an s1 token. The internal counters
  -- are independent, so s2 has never issued this id and returns
  -- Nothing — until s2 happens to have issued a token with the same
  -- internal id. (See README for why this is a real-life limitation
  -- of the int-id encoding and how a closure-keyed map would fix it.)
  r2 <- s2.unseal k
  putStrLn ("s2.unseal(s1.seal(42)) = " ++ show r2)

  -- Demonstrate the cross-sealer limitation: have s2 also seal
  -- something, then try the cross-unseal.
  _ <- s2.seal 99
  r3 <- s2.unseal k          -- k is token#0; s2's tbl now has 99 at 0
  putStrLn ("after s2.seal 99, s2.unseal(s1.seal(42)) = " ++ show r3 ++
           "   <-- collision because token identity is just an int")
