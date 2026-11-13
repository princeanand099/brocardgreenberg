# Manuscript-to-Lean Theorem Correspondence Record

This file tracks every substantive mathematical definition, lemma, proposition, theorem, corollary, and remark claim in the manuscript *"Valuation-Parity Equidistribution, Quadratic Pell Capacity, and Support-Reduced Padé–Wronskian Bounds for the Brocard–Ramanujan Equation"*, its location in the manuscript, its Lean 4 module and declaration, its dependencies, its statement-fidelity status, and its proof status.

## Status Key
- **Fidelity**: `Pending` | `Verified Faithful` | `Corrected (See Audit)`
- **Proof Status**: `Not Started` | `Translated (sorry)` | `Implemented` | `Locally Checked` | `CI Verified` | `Fully Verified`

---

## Section 1: Foundational Definitions and Main Theorems

| Manuscript Item | Location | Lean Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| Eq (1.1) Brocard–Ramanujan equation | §1.1, p. 1 | `BrocardFormalization.Basic` | `IsBrocardSol` | Mathlib `Nat.factorial` | Verified Faithful | Definition |
| Eq (1.2) Counting functions $\mathcal{N}_{P,s}(N), \mathcal{N}_{\text{Brocard}}(N)$ | §1.1, p. 1–2 | `BrocardFormalization.Basic` | `polyFactorialCount`, `brocardCount` | `IsBrocardSol` | Verified Faithful | Definition |
| Eq (1.4) Core/square factorization $n! = q_n s_n^2$, $\mathcal{P}_{\text{odd}}(n), \mathcal{P}_{\text{even}}(n)$ | §1.2, p. 2 | `BrocardFormalization.Basic` | `Podd`, `Peven`, `qn`, `sn`, `factorial_eq_qn_mul_sn_sq` | `padicValNat` | Verified Faithful | Proved (CI Verified) |
| §1.4 Arithmetic invariants (`core`, `rad`, `ω`, `P⁺`, `A*`, `ϑ`, `π`) | §1.4, p. 5 | `BrocardFormalization.Basic` | `coreNat`, `radNat`, `omegaNat`, `largestPrimeFactor`, `oddPart` | Mathlib `Nat.factorization` | Verified Faithful | Proved (CI Verified) |
| Eq (1.5) Fundamental Pell unit & Pell index $k$ | §1.2, p. 2 | `BrocardFormalization.PellAndIwasawa` | `pellFundUnit`, `pellIndex` | `qn`, `Pell.Solution₁` | Verified Faithful | Translated (`sorry`) |
| **Theorem 1.1** (Unconditional Collapse of Pell Index) | §1.2, p. 2 | `BrocardFormalization.PellAndIwasawa` | `theorem_1_1` | `Lemma 3.1`, `Lemma 3.2`, `Theorem 2.5` | Verified Faithful | Translated (`sorry`) |
| **Theorem 1.2** (Non-Vanishing of Iwasawa $\lambda_p$ & Greenberg Conditional Finiteness) | §1.2, p. 2–3 | `BrocardFormalization.PellAndIwasawa` | `theorem_1_2` | `Theorem 1.1`, `Lemma 3.1`, Leopoldt/Ferrero–Washington/Mazur–Wiles | Verified Faithful | Translated (`sorry`) |
| **Theorem 1.3(i)** (Extreme Sparsity of $k=2$) | §1.2, p. 3 | `BrocardFormalization.PairwiseDuality` | `theorem_1_3_i` | `Theorem 6.5` | Verified Faithful | Translated (`sorry`) |
| **Theorem 1.3(ii)** (Global $N^{6/7+\varepsilon}$ & Monomial-Product Bounds) | §1.2, p. 3 | `BrocardFormalization.PadeWronskian` | `theorem_1_3_ii` | `Lemmas 7.1–7.4` | Corrected (See Audit Item 7) | Translated (`sorry`) |

## Section 2: Valuation-Parity Equidistribution of Factorials

| Manuscript Item | Location | Lean Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| Eqs (2.1)–(2.3) $S_{\text{odd}}, S_{\text{even}}, \Delta_{\text{parity}}, \Sigma_{\text{parity}}, \Sigma^*_{\text{parity}}$ | §2, p. 6 | `BrocardFormalization.Basic` | `Sodd`, `Seven`, `DeltaParity`, `SigmaParity`, `SigmaParityStar` | `Podd`, `Peven` | Verified Faithful | Proved (CI Verified) |
| **Lemma 2.1** (Harmonic Layer Stratification & Asymptotics of $\mathcal{P}_{\text{odd}}(n), \log q_n$) | §2.1, p. 6–7 | `BrocardFormalization.ValuationParity` | `lemma_2_1_i`, `lemma_2_1_ii` | `padicValNat_factorial`, PNT (dlVP) | Verified Faithful | Translated (`sorry`) |
| **Lemma 2.2** (Exact Legendre Base-$p$ Reduction on $3 \le p \le \sqrt{n}$) | §2.2, p. 7 | `BrocardFormalization.ValuationParity` | `lemma_2_2_i`, `lemma_2_2_ii` | `sub_one_mul_padicValNat_factorial`, `Chebyshev.pi_le_log4_mul_div` | Verified Faithful | Translated (`sorry`) |
| **Lemma 2.3** (Vaaler's Trigonometric Polynomial Approximation & Even-Harmonic Cancellation) | §2.3, p. 7–8 | `BrocardFormalization.ValuationParity` | `lemma_2_3` | Vaaler [60, Thm 18] | Verified Faithful | Translated (`sorry`) |
| **Lemma 2.4** (Prime Exponential Sum Bound on $[n^\delta, n/(\log n)^{12}]$) | §2.3, p. 8–10 | `BrocardFormalization.ValuationParity` | `lemma_2_4_i`, `lemma_2_4_ii` | Vaughan/van der Corput/Weyl [30] | Corrected (See Audit Item 1) | Translated (`sorry`) |
| **Theorem 2.5** (Valuation-Parity Equidistribution & Second-Order Discrepancy) | §2.3, p. 10–11 | `BrocardFormalization.ValuationParity` | `theorem_2_5_i`, `theorem_2_5_ii`, `theorem_2_5_iii` | `Lemmas 2.1–2.4`, Mertens | Verified Faithful | Translated (`sorry`) |
| **Proposition 2.6** (Jessen–Wintner Rademacher Limit Distribution) | §2.3, p. 11 | `BrocardFormalization.ValuationParity` | `prop_2_6` | `Lemma 2.2(i)`, CRT, Jessen–Wintner | Verified Faithful | Translated (`sorry`) |

## Section 3: Chebyshev–Lucas Valuation Absorption and Pell/Iwasawa Proofs

| Manuscript Item | Location | Lean Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| **Lemma 3.1** (Fundamental Unit Norm & Growth of $q_n, s_n$) | §3.1, p. 12 | `BrocardFormalization.PellAndIwasawa` | `lemma_3_1_i`, `lemma_3_1_ii` | `Pell`, Breusch [8], Rosser–Schoenfeld [48] | Verified Faithful | Translated (`sorry`) |
| **Lemma 3.2** (Chebyshev–Lucas Factorization & $p$-Adic LTE) | §3.1, p. 12–13 | `BrocardFormalization.PellAndIwasawa` | `lemma_3_2_i`, `lemma_3_2_ii` | `Polynomial.Chebyshev` | Verified Faithful | Translated (`sorry`) |
| **Remark 3.3** (Dual Even-Valuation Elimination of Odd Prime Divisors $\ell \ge 3$ of $k$) | §3.2, p. 13 | `BrocardFormalization.PellAndIwasawa` | `remark_3_3` | `Lemma 3.2(i)`, `Theorem 2.5(ii)` | Verified Faithful | Translated (`sorry`) |
| **Proposition 3.4** (Rank-of-Apparition Collapse on $I_2 = (n/3, n/2]$) | §3.2, p. 14 | `BrocardFormalization.PellAndIwasawa` | `prop_3_4` | `Theorem 1.1`, `Lemma 2.1(i)`, `Lemma 3.2(ii)` | Verified Faithful | Translated (`sorry`) |
| **Corollary 3.5** (Rational Fermat Quotient Locks & Sinnott Circular-Unit Congruence) | §3.3, p. 15 | `BrocardFormalization.PellAndIwasawa` | `cor_3_5` | `Theorem 1.2`, Sinnott [54], Kummer congruence [61] | Corrected (See Audit Item 2) | Translated (`sorry`) |
| **Theorem 3.6** (Imaginary Quadratic Picard 2-Torsion Dichotomy) | §3.3, p. 15 | `BrocardFormalization.PellAndIwasawa` | `theorem_3_6` | `Theorem 1.1`, `Lemma 3.1(i)` | Verified Faithful | Translated (`sorry`) |

## Section 4: Arithmetic Structure of the Critical Regime $k = 2$

| Manuscript Item | Location | Lean Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| Eqs (4.1)–(4.3) Three-consecutive-integer factorization | §4.1, p. 16 | `BrocardFormalization.CriticalRegimeK2` | `critical_eqs_4_1_to_4_3` | `Theorem 3.6`, `Pell` | Verified Faithful | Translated (`sorry`) |
| **Proposition 4.1** ($(n/2)$-Smoothness of $m+1$, Biquadratic Splitting, Fermat-Quotient Lock) | §4.1, p. 16 | `BrocardFormalization.CriticalRegimeK2` | `prop_4_1` | `Lemma 2.1` | Verified Faithful | Translated (`sorry`) |
| **Theorem 4.2** (Two-Stage Euclidean Division Quartic Law & Midpoint Core Bounds) | §4.1, p. 17–19 | `BrocardFormalization.CriticalRegimeK2` | `theorem_4_2_i`, `theorem_4_2_ii`, `theorem_4_2_iii` | `Prop 4.1`, `Theorem 2.5`, Mertens | Verified Faithful | Translated (`sorry`) |
| **Lemma 4.3** (Stickelberger's $p$-Adic Factorial Congruence) | §4.2, p. 19 | `BrocardFormalization.CriticalRegimeK2` | `lemma_4_3`, `lemma_4_3_indexed` | `Nat.wilsons_lemma` | Verified Faithful | Translated (`sorry`) |
| **Theorem 4.4** (Stickelberger Base-$p$ Reciprocity, Inert Absorption, Residue Lock) | §4.2, p. 19–20 | `BrocardFormalization.CriticalRegimeK2` | `theorem_4_4_i`, `theorem_4_4_ii` | `Lemma 4.3`, `Prop 4.1`, `Theorem 4.2(i)` | Verified Faithful | Translated (`sorry`) |

## Section 5: The Fundamental Regime $k = 1$ and Rédei–Reichardt Cohomology

| Manuscript Item | Location | Lean Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| **Proposition 5.1** (Continued-Fraction Midpoint Denominator & Conductor Bias) | §5.1, p. 21 | `BrocardFormalization.FundamentalRegimeK1` | `prop_5_1_i`, `prop_5_1_ii` | `Lemma 3.1(i)`, Lagrange CF symmetry [43] | Verified Faithful | Translated (`sorry`) |
| **Theorem 5.2** (Midpoint Core Bipartition, Cross-Symmetry, Radical & Landau–Siegel Bounds) | §5.1, p. 22–23 | `BrocardFormalization.FundamentalRegimeK1` | `theorem_5_2_i`, `theorem_5_2_ii` | `Prop 5.1`, `Theorem 2.5`, Explicit formula [18] | Verified Faithful | Translated (`sorry`) |
| **Lemma 5.3** (Homogeneous Laplacian Equivalence, 2-Adic Cascade, Wolstenholme Evaluation) | §5.2, p. 23–24 | `BrocardFormalization.FundamentalRegimeK1` | `lemma_5_3_i`, `lemma_5_3_ii` | `ZMod`, `Nat.wilsons_lemma` | Verified Faithful | Translated (`sorry`) |
| **Proposition 5.4** (Explicit $\mathbb{F}_2$ Block Structure & All-Ones Reciprocity Duality) | §5.2, p. 24 | `BrocardFormalization.FundamentalRegimeK1` | `prop_5_4` | `Lemma 5.3`, `jacobiSym` | Corrected (See Audit Item 3) | Translated (`sorry`) |
| **Theorem 5.5** (Rédei–Reichardt 4-Rank Cohomology & Reduced Dual Quartic Laws) | §5.2, p. 25 | `BrocardFormalization.FundamentalRegimeK1` | `theorem_5_5_i`, `theorem_5_5_ii` | Hasse/Gauss/Rédei–Reichardt, `Lemma 5.3` | Verified Faithful | Translated (`sorry`) |

## Section 6: Pairwise $\mathrm{SL}_2(\mathbb{Z})$ Duality and Capacity Diamond

| Manuscript Item | Location | Lean Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| **Theorem 6.1** (Universal $\mathrm{SL}_2(\mathbb{Z})$ Four-GCD System & Twin Norm Identities) | §6.1, p. 26–27 | `BrocardFormalization.PairwiseDuality` | `theorem_6_1` | `Nat.gcd`, `QuadraticAlgebra` | Verified Faithful | Translated (`sorry`) |
| **Proposition 6.2** (Quadratic-Radical Identities, Quartic Thue, $X$-Splitting, Pfaffian System) | §6.1, p. 27–28 | `BrocardFormalization.PairwiseDuality` | `prop_6_2_i`, `prop_6_2_ii`, `prop_6_2_iii`, `prop_6_2_iv` | `Theorem 6.1` | Corrected (See Audit Item 4) | Translated (`sorry`) |
| **Theorem 6.3** (Consecutive-Index Rigidity & Square-Shift Exclusions) | §6.2, p. 28–29 | `BrocardFormalization.PairwiseDuality` | `theorem_6_3_i`, `theorem_6_3_ii`, `theorem_6_3_iii` | `Theorem 6.1`, `Theorem 2.5(ii)` | Verified Faithful | Translated (`sorry`) |
| **Lemma 6.4** (Odd-Harmonic Vaaler Diagonal Non-Vanishing for Parity-Flip Primes) | §6.3, p. 29–30 | `BrocardFormalization.PairwiseDuality` | `lemma_6_4` | `Lemma 2.3`, `Lemma 2.4`, Mertens | Verified Faithful | Translated (`sorry`) |
| **Theorem 6.5** (Universal Capacity Diamond & Rankin Spherical Cap Bound) | §6.3, p. 30–31 | `BrocardFormalization.PairwiseDuality` | `theorem_6_5` | `Theorem 6.1`, `Theorem 5.2(i)`, `Lemma 6.4` | Corrected (See Audit Item 5) | Translated (`sorry`) |

## Section 7: Support-Reduced Padé–Wronskian Approximations

| Manuscript Item | Location | Lean Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| **Lemma 7.1** (Initial $(m+1)$-Variable Padé Polynomials via Siegel's Lemma) | §7.1, p. 32–33 | `BrocardFormalization.PadeWronskian` | `lemma_7_1` | `Int.Matrix.exists_ne_zero_int_vec_norm_le` | Corrected (See Audit Item 7) | Translated (`sorry`) |
| **Lemma 7.2** (Linear Independence of Monomial Products over $\mathbb{C}(x)$) | §7.2, p. 33 | `BrocardFormalization.PadeWronskian` | `lemma_7_2` | Puiseux expansion | Verified Faithful | Translated (`sorry`) |
| **Lemma 7.3** (Support-Reduced Wronskian Non-Vanishing & Gauss's Lemma Bound) | §7.2, p. 34–35 | `BrocardFormalization.PadeWronskian` | `lemma_7_3_i`, `lemma_7_3_ii`, `lemma_7_3_iii` | `Lemma 7.1`, `Lemma 7.2`, Siegel differential lemma | Corrected (See Audit Items 6–7) | Translated (`sorry`) |
| **Lemma 7.4** (Leibniz Derivative Estimates & Factorial-Root Approximation) | §7.2, p. 35 | `BrocardFormalization.PadeWronskian` | `lemma_7_4_i`, `lemma_7_4_ii` | `Lemma 7.1`, `Lemma 7.3` | Corrected (See Audit Item 7) | Translated (`sorry`) |
| **Theorem 7.5** (Unconditional Finiteness for $n!+A=m^k$ outside $n!+c^2=m^2$) | §7.4, p. 38 | `BrocardFormalization.PadeWronskian` | `theorem_7_5` | Grunwald–Wang [1], Chebotarev [59], Berend–Harmse [5] | Corrected (See Audit Item 8) | Translated (`sorry`) |

## Section 8: Harmonic Analysis on the CRT Torus and $p$-Adic Binomial Lifting

| Manuscript Item | Location | Lean Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| **Theorem 8.1** (CRT Partition of Unity, Punctured Discrepancy, Projection, Locked-Torus) | §8.1, p. 39–40 | `BrocardFormalization.CRTTorus` | `theorem_8_1_i`, `theorem_8_1_ii`, `theorem_8_1_iii` | `ZMod.chineseRemainder`, `Theorem 5.5(ii)`, `Theorem 2.5(i)` | Verified Faithful | Translated (`sorry`) |
| **Theorem 8.2** (Resonance-Free $L^{2k}$ Parseval Identities & $p$-Adic Binomial Lifting) | §8.2, p. 40–41 | `BrocardFormalization.CRTTorus` | `theorem_8_2_i`, `theorem_8_2_ii` | `ZMod.chineseRemainder`, `Hensel` | Verified Faithful | Translated (`sorry`) |
| **Theorem 8.3** (Fourth-Order Subgaussian Tail & Beurling–Selberg–Hölder Arc Bound) | §8.3, p. 41–42 | `BrocardFormalization.CRTTorus` | `theorem_8_3_i`, `theorem_8_3_ii` | `Theorem 8.2(i)`, Vaaler [60, Thm 19] | Corrected (See Audit Item 9) | Translated (`sorry`) |
| **Theorem 8.4** (External Wilson QR Sieve & Macroscopic Sieve Independence) | §8.3, p. 42 | `BrocardFormalization.CRTTorus` | `theorem_8_4_i`, `theorem_8_4_ii` | `Nat.wilsons_lemma`, Bourgain–Demeter–Guth [3], Davis [19], Erdős–Turán [22] | Verified Faithful | Translated (`sorry`) |

## Section 9: Frey–Hellegouarch Elliptic Curves and Analytic Thresholds

| Manuscript Item | Location | Lean Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| **Theorem 9.1** (Frey Curves $\mathcal{E}_n, F_n^{(2)}$, Level-2 CM Reduction, $abc$ Quality) | §9.1, p. 43–44 | `BrocardFormalization.FreyCurvesAndThresholds` | `theorem_9_1_i`, `theorem_9_1_ii` | `WeierstrassCurve`, `Theorem 1.1`, `Theorem 4.2(i)`, Wiles/Mazur/Kenku/Serre | Verified Faithful | Translated (`sorry`) |
| **Theorem 9.2** (Effective Tatuzawa Class Number Explosion & Conditional Finiteness (C1)–(C5)) | §9.2, p. 44–45 | `BrocardFormalization.FreyCurvesAndThresholds` | `theorem_9_2_i`, `theorem_9_2_ii` | Dirichlet CNF, Tatuzawa [58], `Theorem 1.1`, `Lemmas/Props` | Corrected (See Audit Item 10) | Translated (`sorry`) |
| **Proposition 9.3** (Ribet Level-Lowering, Matveev–Yu Rank, Short Character Sum Thresholds) | §9.3, p. 45–46 | `BrocardFormalization.FreyCurvesAndThresholds` | `prop_9_3_i`, `prop_9_3_ii`, `prop_9_3_iii` | `Theorem 5.2(i)`, `Theorem 4.2(i)`, `Prop 5.1(ii)`, `Theorem 6.1(iii)`, Ribet/Matveev/Yu | Verified Faithful | Translated (`sorry`) |
