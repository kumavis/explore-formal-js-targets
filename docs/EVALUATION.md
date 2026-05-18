# Evaluation: Dafny vs Agda vs Idris2 JavaScript backends

Auto-generated summary of three dimensions:

1. **Readability of the emitted JavaScript**
2. **SES (Hardened JavaScript) compatibility**
3. **Ease of interacting with objects from the outer JavaScript world**

## Aggregate metrics

| Problem | Lang | src LOC | compiled bytes | needs bundling | static scan | lockdown+require | raw compartment | bundled compartment |
| --- | --- | ---: | ---: | :---: | :---: | :---: | :---: | :---: |
| factorial | Dafny | 31 | 32,337 | **yes** | ✅ | ✅ | ❌ | ❌ |
| factorial | Agda | 40 | 12,424 | **yes** | ✅ | ✅ | ❌ | ✅ |
| factorial | Idris2 | 22 | 10,221 | no | ✅ | ✅ | ✅ | ✅ |
| reverse | Dafny | 38 | 32,211 | **yes** | ✅ | ✅ | ❌ | ❌ |
| reverse | Agda | 60 | 12,763 | **yes** | ✅ | ✅ | ❌ | ✅ |
| reverse | Idris2 | 34 | 11,850 | no | ✅ | ✅ | ✅ | ✅ |
| insertion-sort | Dafny | 78 | 32,545 | **yes** | ✅ | ✅ | ❌ | ❌ |
| insertion-sort | Agda | 92 | 16,957 | **yes** | ✅ | ✅ | ❌ | ✅ |
| insertion-sort | Idris2 | 79 | 12,317 | no | ✅ | ✅ | ✅ | ✅ |

Legend: ✅ pass, ❌ fail, — not applicable.

See [hand-written notes](../EVALUATION.md) for the qualitative analysis (FFI ergonomics, readability commentary, etc.).