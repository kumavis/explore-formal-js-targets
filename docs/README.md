# Verified-Program JS Backend Comparison

This directory holds an auto-generated, per-problem comparison of Dafny, Agda, and Idris2 JavaScript output, plus SES compatibility probes. See [EVALUATION.md](./EVALUATION.md) for the overall evaluation.

## Problems

- [Factorial (with positivity proof)](./factorial.md)
- [List reverse (with reverse-reverse-identity proof)](./reverse.md)
- [Insertion sort (with sortedness proof)](./insertion-sort.md)
- [Vec.zipWith (length-indexed vectors)](./vec-zipwith.md)
- [Triangular-number closed form (2·Σ n = n·(n+1))](./sum-formula.md)

## How to regenerate

```
nix develop  # or: have dafny, agda, idris2, nodejs on PATH
npm install
npm run all
```