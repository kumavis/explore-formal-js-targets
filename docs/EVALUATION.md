# Evaluation: Dafny vs Agda vs Idris2 JavaScript backends

Auto-generated summary of three dimensions:

1. **Readability of the emitted JavaScript**
2. **SES (Hardened JavaScript) compatibility**
3. **Ease of interacting with objects from the outer JavaScript world**

## Aggregate metrics

| Problem | Lang | src LOC | compiled bytes | static SES findings | lockdown+require | compartment |
| --- | --- | ---: | ---: | --- | --- | --- |
| factorial | Dafny | 31 | 32,337 | none | pass | evaluate-failed |
| factorial | Agda | 40 | 12,424 | none | pass | evaluate-failed |
| factorial | Idris2 | 22 | 10,221 | none | pass | pass |
| reverse | Dafny | 38 | 32,211 | none | pass | evaluate-failed |
| reverse | Agda | 60 | 12,763 | none | pass | evaluate-failed |
| reverse | Idris2 | 34 | 11,850 | none | pass | pass |
| insertion-sort | Dafny | 78 | 32,545 | none | pass | evaluate-failed |
| insertion-sort | Agda | 92 | 16,957 | none | pass | evaluate-failed |
| insertion-sort | Idris2 | 79 | 12,317 | none | pass | pass |

See [hand-written notes](../EVALUATION.md) for the qualitative analysis (FFI ergonomics, readability commentary, etc.).