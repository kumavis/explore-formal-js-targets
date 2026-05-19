# Evaluation: Dafny vs Agda vs Idris2 JavaScript backends

Auto-generated summary of three dimensions:

1. **Readability of the emitted JavaScript**
2. **SES (Hardened JavaScript) compatibility**
3. **Ease of interacting with objects from the outer JavaScript world**

## Aggregate metrics

| Problem | Lang | src LOC | compiled JS (solution + library = total) | needs bundling | static scan | lockdown+require | raw compartment | bundled compartment | endowments |
| --- | --- | ---: | ---: | :---: | :---: | :---: | :---: | :---: | --- |
| factorial | Dafny | 31 | 1,499 + 30,838 = 32,337 | **yes** | ✅ | ✅ | ❌ | ✅ | `console` + `BigNumber` + `Math` |
| factorial | Agda | 40 | 1,565 + 14,926 = 16,491 | **yes** | ✅ | ✅ | ❌ | ✅ | `console` |
| factorial | Idris2 | 22 | 403 + 9,818 = 10,221 | no | ✅ | ✅ | ✅ | ✅ | `console` |
| reverse | Dafny | 38 | 1,375 + 30,836 = 32,211 | **yes** | ✅ | ✅ | ❌ | ✅ | `console` + `BigNumber` + `Math` |
| reverse | Agda | 60 | 1,904 + 14,926 = 16,830 | **yes** | ✅ | ✅ | ❌ | ✅ | `console` |
| reverse | Idris2 | 34 | 612 + 11,238 = 11,850 | no | ✅ | ✅ | ✅ | ✅ | `console` |
| insertion-sort | Dafny | 78 | 1,703 + 30,842 = 32,545 | **yes** | ✅ | ✅ | ❌ | ✅ | `console` + `BigNumber` + `Math` |
| insertion-sort | Agda | 92 | 6,098 + 14,759 = 20,857 | **yes** | ✅ | ✅ | ❌ | ✅ | `console` |
| insertion-sort | Idris2 | 79 | 1,477 + 10,840 = 12,317 | no | ✅ | ✅ | ✅ | ✅ | `console` |
| vec-zipwith | Dafny | 28 | 1,749 + 30,839 = 32,588 | **yes** | ✅ | ✅ | ❌ | ✅ | `console` + `BigNumber` + `Math` |
| vec-zipwith | Agda | 52 | 2,052 + 14,759 = 16,811 | **yes** | ✅ | ✅ | ❌ | ✅ | `console` |
| vec-zipwith | Idris2 | 33 | 605 + 11,014 = 11,619 | no | ✅ | ✅ | ✅ | ✅ | `console` |
| sum-formula | Dafny | 29 | 1,598 + 30,839 = 32,437 | **yes** | ✅ | ✅ | ❌ | ✅ | `console` + `BigNumber` + `Math` |
| sum-formula | Agda | 116 | 1,780 + 14,926 = 16,706 | **yes** | ✅ | ✅ | ❌ | ✅ | `console` |
| sum-formula | Idris2 | 44 | 263 + 10,102 = 10,365 | no | ✅ | ✅ | ✅ | ✅ | `console` |

Legend: ✅ pass, ❌ fail, — not applicable.

**Dafny note:** the bundled-compartment column passes only because we endow `Math`. Dafny's `bignumber.js` runtime calls `Math.random()` at module init and secure-mode SES `Math` removes `random`.

See [hand-written notes](../EVALUATION.md) for the qualitative analysis (FFI ergonomics, readability commentary, etc.).