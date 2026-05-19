# jesc24 OCAP patterns, in four languages

Ports of operational shapes from
[`agoric-labs/jesc24`](https://github.com/agoric-labs/jesc24/tree/main/theories/heap_lang/lib).
Each pattern is implemented in Dafny, Agda, Idris2, and Coq; per-pattern
READMEs compare what each language's tooling can guarantee at the seam.

We don't reproduce jesc24's Iris separation-logic proofs — those live
in hundreds of lines of `iProp Σ` over ghost state. The goal here is
to match the *runtime shape* and surface where each language's
tooling falls short of OCAP-grade safety.

| Pattern | Description | Where |
| --- | --- | --- |
| Sealer | `make_seal` returns `(seal, unseal)`. Cross-sealer tokens are not unsealable. | [`sealer/`](./sealer/) |
| Caretaker | Revocable forwarder. `make_caretaker` returns `{ wrap, enable, disable }`. After `disable`, every `wrap` fails. | [`caretaker/`](./caretaker/) |

Each pattern subdirectory has one source file per language (plus an
OCaml driver for the Coq port) and a `README.md` discussing the
mechanisms.
