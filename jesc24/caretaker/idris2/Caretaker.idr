||| Revocable caretaker, after agoric-labs/jesc24's
||| `theories/heap_lang/lib/caretaker.v`.
|||
||| A *caretaker* wraps an underlying target function `f`. While
||| *enabled*, `wrap v` calls `f v` and returns the result. While
||| *disabled*, `wrap v` refuses (returns `Nothing` here; jesc24's
||| version `abort`s). `enable` / `disable` toggle the flag.
|||
||| This is the canonical OCAP revocation primitive: a holder of the
||| caretaker can pass `wrap` to an untrusted party, then `disable`
||| to revoke all *future* access without ever sharing the underlying
||| `f` directly.

module Main

import Data.IORef

record Caretaker where
  constructor MkCaretaker
  wrap    : Nat -> IO (Maybe Nat)
  enable  : IO ()
  disable : IO ()

makeCaretaker : (Nat -> Nat) -> IO Caretaker
makeCaretaker f = do
  enabledRef <- newIORef False
  let wrap' : Nat -> IO (Maybe Nat)
      wrap' v = do
        en <- readIORef enabledRef
        if en then pure (Just (f v)) else pure Nothing
  let enable'  : IO () = writeIORef enabledRef True
  let disable' : IO () = writeIORef enabledRef False
  pure (MkCaretaker wrap' enable' disable')

main : IO ()
main = do
  c <- makeCaretaker (\n => n * 2)

  -- Default: disabled. Wrapping refuses.
  r0 <- c.wrap 10
  putStrLn ("default (disabled): wrap 10 = " ++ show r0)

  c.enable
  r1 <- c.wrap 10
  putStrLn ("enabled:            wrap 10 = " ++ show r1)
  r2 <- c.wrap 7
  putStrLn ("enabled:            wrap 7  = " ++ show r2)

  c.disable
  r3 <- c.wrap 10
  putStrLn ("disabled:           wrap 10 = " ++ show r3)
