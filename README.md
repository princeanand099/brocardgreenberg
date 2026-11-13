# Brocard–Ramanujan Lean 4 Formalization

Formalization in Lean 4 of *"Valuation-Parity Equidistribution, Quadratic Pell Capacity, and Support-Reduced Padé–Wronskian Bounds for the Brocard–Ramanujan Equation"*.

## Environment & Versions
- **Lean**: `leanprover/lean4:v4.35.0`
- **Mathlib**: `v4.35.0`
- **Build System**: Lake 5.0.0

## Build Instructions
```bash
lake exe cache get
lake build
```

## Repository Structure
- `BrocardFormalization.lean`: Root module importing all formalization modules.
- `BrocardFormalization/Basic.lean`: Foundational definitions and notation (§1.1–1.4, §2 eqs. 2.1–2.3).
- `BrocardFormalization/ExternalAxioms.lean`: Strictly scoped external established results from peer-reviewed literature.
- `BrocardFormalization/ValuationParity.lean`: Section 2 — Valuation-parity equidistribution of factorials.
- `BrocardFormalization/PellAndIwasawa.lean`: Section 3 & Theorems 1.1, 1.2 — Pell index collapse and Iwasawa invariants.
- `BrocardFormalization/CriticalRegimeK2.lean`: Section 4 — Critical regime $k = 2$, quartic Euclidean laws, Stickelberger reciprocity.
- `BrocardFormalization/FundamentalRegimeK1.lean`: Section 5 — Fundamental regime $k = 1$, Landau–Siegel core bounds, Rédei–Reichardt cohomology.
- `BrocardFormalization/PairwiseDuality.lean`: Section 6 & Theorem 1.3(i) — Universal $\mathrm{SL}_2(\mathbb{Z})$ four-GCD duality and Capacity Diamond.
- `BrocardFormalization/PadeWronskian.lean`: Section 7 & Theorem 1.3(ii) — Support-reduced Padé–Wronskian bounds and $n! + A = m^k$ finiteness.
- `BrocardFormalization/CRTTorus.lean`: Section 8 — CRT torus harmonic analysis and $p$-adic binomial lifting.
- `BrocardFormalization/FreyCurvesAndThresholds.lean`: Section 9 — Frey–Hellegouarch elliptic curves, Tatuzawa class-number bounds, and analytic thresholds.
- `BrocardFormalization/MainTheorems.lean`: Top-level statements and axiom dependency checks.

## Documentation & Audit Records
- `THEOREM_CORRESPONDENCE.md`: Complete manuscript-to-Lean correspondence table.
- `EXTERNAL_AXIOMS.md`: Register of external axioms with exact literature citations.
- `CORRECTION_AUDIT.md`: Mathematical correction and audit record.
- `PROGRESS.md`: Continuous progress log.

## Status
Stage 3 (faithful translation across all 11 modules) compiles cleanly via `lake build`. Stage 4–5 formalization is in progress to eliminate all temporary `sorry` proofs; do not treat results as fully verified until Stage 7 final verification passes.
