# External Axiom Register

## Strict Policy
External axioms are permitted **only** for established mathematical results external to the manuscript's own contribution where no suitable formalization exists in Lean 4 / Mathlib v4.35.0. Every external axiom satisfies:
1. Established in credible peer-reviewed mathematical literature.
2. Exact published source identifiable in the manuscript bibliography `[1]–[64]`.
3. Source supports the precise mathematical statement introduced, with no unnecessary strengthening.
4. Not a lemma, proposition, corollary, or theorem the manuscript is responsible for proving.
5. Recorded here with complete statement, published source, justification, and dependent declarations.

No manuscript-owned Vaughan decomposition, Type I/II Cauchy–Schwarz bound, projective rank-of-apparition bound, or normalized Wronskian rank lemma is axiomatized here.

---

## Registered External Axioms (`BrocardFormalization.External`)

### 1. Analytic Prime Number Theory
1. **`deLaValleePoussin_pnt`**
   - **Source**: H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Springer, 2000 ([18, Chapter 18]).
   - **Statement**: Effective constants $c_1, C > 0$ such that $|\vartheta(x) - x| \le C x \exp(-c_1\sqrt{\log x})$ and $|\pi(x) - \operatorname{li}(x)| \le C x \exp(-c_1\sqrt{\log x})$ for all $x \ge 2$.
   - **Justification**: Zero-free region and effective PNT error term for $\vartheta(x)$ and $\pi(x)$ are not yet in Mathlib v4.35.0.
   - **Dependent declarations**: `lemma_2_1_ii`, `theorem_2_5_i`, `theorem_5_2_ii`, `prop_9_3_i`.

2. **`mertens_first_theorem`**
   - **Source**: H. Davenport, *Multiplicative Number Theory*, 3rd ed. ([18, Chapter 7]).
   - **Statement**: $\sum_{3 \le p \le x} \frac{\log p}{p - 1} = \log x - \gamma - \log 2 + o(1)$ (where $\gamma = \text{Real.eulerMascheroniConstant}$) and $\sum_{2 \le p \le x} \frac{\log p}{p} = \log x + O(1)$.
   - **Justification**: Sharp $\gamma + \log 2$ constant in Mertens' first theorem is not formalized in Mathlib v4.35.0.
   - **Dependent declarations**: `theorem_2_5_ii`, `theorem_4_2_iii`, `lemma_6_4`, `prop_9_3_ii`.

3. **`pnt_arithmetic_progression`**
   - **Source**: H. Davenport, *Multiplicative Number Theory*, 3rd ed. ([18, Chapter 20]).
   - **Statement**: $\sum_{p \le x,\, p \equiv a \pmod q} \log p = \frac{x}{\varphi(q)} + o(x)$ for fixed $q \ge 1$ and $\gcd(a,q)=1$.
   - **Justification**: Non-vanishing of $L(1, \chi)$ and PNT in arithmetic progressions are not in Mathlib v4.35.0.
   - **Dependent declarations**: `theorem_7_5`.

4. **`breusch_bertrand_mod_four`**
   - **Source**: R. Breusch, *Math. Z.* 34 (1932), 505–526 ([8]).
   - **Statement**: For every real $x \ge 7$, there is a prime $p \in (x, 2x]$ with $p \equiv 3 \pmod 4$.
   - **Justification**: Explicit Bertrand postulate in residue classes mod 4 is not in Mathlib v4.35.0.
   - **Dependent declarations**: `lemma_3_1_i`.

5. **`rosser_schoenfeld_theta_diff`**
   - **Source**: J. B. Rosser and L. Schoenfeld, *Illinois J. Math.* 6 (1962), 64–94, Theorem 10 ([48]).
   - **Statement**: $\vartheta(n) - \vartheta(n/2) > 0.4 n$ for all integers $n \ge 116$.
   - **Justification**: Explicit Rosser–Schoenfeld Chebyshev bounds are not in Mathlib v4.35.0.
   - **Dependent declarations**: `lemma_3_1_i`.

6. **`schoenfeld_prime_gap`**
   - **Source**: L. Schoenfeld, *Math. Comp.* 30 (1976), 337–360 ([50]).
   - **Statement**: $\vartheta(x + x/16597) > \vartheta(x)$ for all real $x \ge 2010760$.
   - **Justification**: Explicit short-interval Chebyshev bound is not in Mathlib v4.35.0.
   - **Dependent declarations**: `theorem_1_1` (distinctness of $q_n$).

7. **`nagura_prime_interval`**
   - **Source**: J. Nagura, *Proc. Japan Acad.* 28 (1952), 177–181 ([41]).
   - **Statement**: For all $x \ge 25$, there exists a prime $p \in (x, \frac{6}{5}x)$.
   - **Justification**: Explicit prime-in-$(x, 6x/5)$ theorem is not in Mathlib v4.35.0.
   - **Dependent declarations**: `theorem_1_2`.

8. **`berndt_galway_brocard_bound`**
   - **Source**: B. C. Berndt and W. F. Galway, *Ramanujan J.* 4 (2000), 41–42 ([7]).
   - **Statement**: $n! + 1 = m^2$ has no positive integer solutions with $8 \le n \le 10^9$.
   - **Justification**: Published peer-reviewed large-scale computational sieve verification up to $10^9$ (infeasible inside kernel `decide` beyond small $n$).
   - **Dependent declarations**: `theorem_1_1`, `theorem_1_2`.

### 2. Trigonometric Polynomials, Exponential Sums, and Diophantine Approximation
9. **`vaaler_sawtooth_approx`**
   - **Source**: J. D. Vaaler, *Bull. Amer. Math. Soc.* 12 (1985), Theorem 18 ([60]).
   - **Statement**: Extremal trigonometric polynomials $\Psi_H, B_H$ with Beurling–Vaaler kernel $W$ approximating $\psi(t) = t - \lfloor t \rfloor - 1/2$.
   - **Justification**: Fourier extremal approximation of sawtooth functions is not in Mathlib v4.35.0.
   - **Dependent declarations**: `lemma_2_3`, `theorem_2_5_i`, `theorem_2_5_ii`, `lemma_6_4`.

10. **`vaaler_indicator_majorant`**
    - **Source**: J. D. Vaaler, *Bull. Amer. Math. Soc.* 12 (1985), Theorem 19 ([60]).
    - **Statement**: Degree-$H$ trigonometric polynomial majorant $I^+_H(x) \ge \mathbf{1}_{[-\delta, \delta]}(x)$ with Fourier coefficients $|\hat{I}^+_H(h)| \le \hat{I}^+_H(0) = 2\delta + \frac{1}{H+1}$.
    - **Justification**: Beurling–Selberg majorant of interval indicator functions is not in Mathlib v4.35.0.
    - **Dependent declarations**: `theorem_8_3_ii`.

11. **`kusmin_landau_bound`**
    - **Source**: H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloq. Publ. 53, 2004 ([30, Corollary 8.11]).
    - **Statement**: If $F'$ is monotonic on $[a,b]$ with $\lambda_1 \le |F'(t)| \le 1/2$, then $\left\|\sum_{\lceil a \rceil \le m \le \lfloor b \rfloor} e(F(m))\right\| \le C/\lambda_1$.
    - **Justification**: First-derivative exponential sum bound is not in Mathlib v4.35.0.
    - **Dependent declarations**: `lemma_2_4_i`.

12. **`van_der_corput_kth_derivative`**
    - **Source**: H. Iwaniec and E. Kowalski, *Analytic Number Theory* ([30, Theorem 8.4 & Corollary 8.13]).
    - **Statement**: For $k \ge 2$ and $\lambda \le |F^{(k)}(t)| \le \alpha\lambda$ on $[a,b]$ ($b-a \ge 1$), $\left\|\sum_{m} e(F(m))\right\| \ll_{k,\alpha} (b-a)(\alpha^2\lambda)^{1/(2^k-2)} + (b-a)^{1-2^{2-k}}\lambda^{-1/(2^k-2)}$.
    - **Justification**: Higher-derivative van der Corput bounds are not in Mathlib v4.35.0.
    - **Dependent declarations**: `lemma_2_4_i`, `lemma_2_4_ii`.

13. **`vinogradov_weyl_derivative_bound`**
    - **Source**: H. Iwaniec and E. Kowalski, *Analytic Number Theory* ([30, Theorem 8.25]).
    - **Statement**: For $k \ge 3$ and $\lambda \in [(b-a)^{-2}, (b-a)^{-1}]$ bounding $|F^{(k)}(t)|$, $\left\|\sum_{m} e(F(m))\right\| \le C_{k,\alpha}(b-a)^{1-\eta_k}$ for some $\eta_k > 0$.
    - **Justification**: Vinogradov mean-value derivative exponential sum bound is not in Mathlib v4.35.0.
    - **Dependent declarations**: `lemma_2_4_i`, `lemma_2_4_ii`.

14. **`davenport_explicit_formula_dirichlet`**
    - **Source**: H. Davenport, *Multiplicative Number Theory*, 3rd ed. ([18, Chapter 19]).
    - **Statement**: Explicit formula for $\sum_{n/2 < p \le n} \chi(p) \log p$ for non-principal real $\chi$ mod $Q \le \exp(2 c_0 \sqrt{\log n})$, separating the optional simple real Siegel zero $\beta_1 \in (1 - c_2/\log Q, 1)$.
    - **Justification**: Zero-free region and explicit formula for Dirichlet $L$-functions are not in Mathlib v4.35.0.
    - **Dependent declarations**: `theorem_5_2_ii`.

15. **`davis_irrationality_measure_e`**
    - **Source**: C. S. Davis, *Bull. Austral. Math. Soc.* 20 (1979), 407–410 ([19]).
    - **Statement**: $|e - p/q| \ge C_\varepsilon / q^{2+\varepsilon}$ for all integers $p, q \ge 1$.
    - **Justification**: Davis's $\mu(e) = 2$ irrationality measure is not in Mathlib v4.35.0.
    - **Dependent declarations**: `theorem_8_4_ii`.

16. **`bourgain_demeter_guth_weyl_bound`**
    - **Source**: H. Weyl ([62]) and J. Bourgain, C. Demeter, L. Guth, *Ann. of Math.* 184 (2016), 633–682 ([3]).
    - **Statement**: Polynomial Weyl sum bound $\left\|\sum_{y=1}^Y e(f(y))\right\| \le C_{k,\varepsilon_1} Y^{1+\varepsilon_1} (q^{-1} + Y^{-1} + q Y^{-k})^{\eta_k}$ for $\eta_k = \max(2^{1-k}, \frac{1}{2k(k-1)})$ given rational approximation $|\alpha - a/q| \le 1/q^2$.
    - **Justification**: Weyl differencing and Bourgain–Demeter–Guth VMVT are not in Mathlib v4.35.0.
    - **Dependent declarations**: `theorem_8_4_ii`.

17. **`erdos_turan_inequality`**
    - **Source**: P. Erdős and P. Turán, *Indag. Math.* 10 (1948), 370–378, 406–413 ([22]).
    - **Statement**: Quantitative bound on discrepancy mod 1 via exponential sums up to harmonic cutoff $H$.
    - **Justification**: Erdős–Turán inequality is not in Mathlib v4.35.0.
    - **Dependent declarations**: `theorem_8_4_ii`.

### 3. Probability and Continued Fractions
18. **`jessen_wintner_rademacher_density`**
    - **Source**: B. Jessen and A. Wintner, *Trans. Amer. Math. Soc.* 38 (1935), 48–88.
    - **Statement**: Existence of a smooth, strictly positive, symmetric probability density $\rho$ with characteristic function $\Phi(\tau) = \prod_{p \ge 3} \cos(\tau \frac{\log p}{p-1})$.
    - **Justification**: Jessen–Wintner law of pure types and infinite product characteristic function density are not in Mathlib v4.35.0.
    - **Dependent declarations**: `prop_2_6`.

19. **`lagrange_continued_fraction_midpoint`**
    - **Source**: O. Perron, *Die Lehre von den Kettenbrüchen*, Band I, 3rd ed., Teubner, 1954 ([43, §25]).
    - **Statement**: When $x^2 - D y^2 = -1$ is insoluble, the regular continued fraction of $\sqrt{D}$ has even period $L = 2M$, and its half-period complete quotient denominator satisfies $Q^*_M = 2^a \operatorname{core}(X_1 \mp 1) < 2\sqrt{D}$, $Q^*_M \mid 2D$.
    - **Justification**: Regular continued fraction midpoint symmetry of quadratic surds is not in Mathlib v4.35.0.
    - **Dependent declarations**: `prop_5_1_i`.

### 4. Iwasawa Theory, Class Field Theory, and Analytic Class Number Theory
20. **`iwasawa_kubota_leopoldt_package`**
    - **Source**: L. C. Washington ([61, Thm 5.24 & Thm 7.10]), B. Ferrero and L. C. Washington ([23]), B. Mazur and A. Wiles ([40]).
    - **Statement**: Coupled to `QuadField (q : ℚ)`, `NumberField.classNumber`, and `Pell.Solution₁`: for unramified $p \ge 5$, gives Leopoldt's $p$-adic class number formula $v_p(L_p(1, \chi_D)) = v_p(h(K)) + v_p(\tilde{R}_p(K)) - 1$, $v_p(\tilde{R}_p(K)) = v_p(s)$, $\mu_p(K) = 0$, and $v_p(L_p(1,\chi_D)) \ge 1 \implies \lambda_p(K) \ge 1$.
    - **Justification**: Kubota–Leopoldt $p$-adic $L$-functions, Ferrero–Washington, and Mazur–Wiles Iwasawa Main Conjecture are not in Mathlib v4.35.0.
    - **Dependent declarations**: `theorem_1_2`.

21. **`sinnott_and_kummer_congruence`**
    - **Source**: W. Sinnott ([54]), L. C. Washington ([61, Thm 5.11]).
    - **Statement**: Coupled to `QuadField (-(3 * q : ℚ))`, `NumberField.classNumber`, and `Pell.Solution₁`: if $3 \nmid q$ and $v_3(s) - v_3(d_n k) \ge 2$, then $3 \mid (1 - \chi_{-3D}(3)) h(\mathbb{Q}(\sqrt{-3q}))$.
    - **Justification**: $p$-adic Kummer congruences between $L_3(1, \chi_D)$ and $B_{1, \chi_{-3D}}$ are not in Mathlib v4.35.0.
    - **Dependent declarations**: `cor_3_5`.

22. **`tatuzawa_effective_siegel`**
    - **Source**: H. Davenport ([18, Ch. 6]), T. Tatuzawa, *Jpn. J. Math.* 21 (1951), 163–178 ([58]).
    - **Statement**: Coupled to `NumberField.classNumber (QuadField q)` and `NumberField.Units.regulator (QuadField q)`: Dirichlet's class number formula and Tatuzawa's lower bound $L(1, \chi_D) > 0.655 \varepsilon D^{-\varepsilon}$ for all fundamental discriminants $D \neq D_*$.
    - **Justification**: Analytic class number formula and Tatuzawa's effective Siegel theorem are not in Mathlib v4.35.0.
    - **Dependent declarations**: `theorem_9_2_i`.

23. **`hasse_gauss_redei_reichardt`**
    - **Source**: C. F. Gauss, *Disquisitiones Arithmeticae* ([24]), Hasse Norm Theorem, Rédei–Reichardt theorem.
    - **Statement**: Coupled to `NumberField.classNumber (QuadField q)`: narrow class group decomposition $\mathrm{Cl}^+(q) \simeq \mathcal{A}_2(q) \oplus \mathrm{Cl}^+_{\mathrm{odd}}(q)$ of order $2 h(K)$, genus rank $\operatorname{rank}_2 \mathcal{A}_2(q) = \omega(D) - 1$, and 4-rank relation.
    - **Justification**: Gauss genus theory and Rédei–Reichardt 4-rank theorem for narrow class groups are not in Mathlib v4.35.0.
    - **Dependent declarations**: `theorem_5_5_i`, `theorem_9_2_i`.

### 5. Differential Wronskians, Galois / Chebotarev, Elliptic Curves, Linear Forms
24. **`siegel_differential_wronskian_lemma`**
    - **Source**: C. L. Siegel, *Transcendental Numbers*, Princeton Univ. Press, 1949 ([53, Chapter 2, Lemma 4]).
    - **Statement**: Given $s \ge 1$ power series $\omega_a \in \mathbb{C}\llbracket X \rrbracket$ satisfying $T \omega_a' = (T A_a) \omega_a$, linearly independent over $\mathbb{C}[x]$ (hence $\mathbb{C}(x)$), and $P_a \in \mathbb{Q}[x] \setminus \{0\}$, the $s \times s$ differential Wronskian $\det(P_a^{[k]}(x))$ is nonzero in $\mathbb{Q}[x]$.
    - **Justification**: Siegel's differential Wronskian non-vanishing lemma (using dimension of linear ODE solution spaces) is not in Mathlib v4.35.0.
    - **Dependent declarations**: `lemma_7_3_i`.

25. **`grunwald_wang_chebotarev_inert_prime`**
    - **Source**: E. Artin and J. Tate ([1, Ch. 10]), N. Tschebotareff ([59]).
    - **Statement**: Existence of a prime $p_0 \nmid kA$ such that $x^k \equiv A \pmod{p_0}$ has no solution when $A \neq c^k$ (and $A \neq 2^{k/2} c^k$ if $8 \mid k$).
    - **Justification**: Grunwald–Wang and Chebotarev density theorems are not in Mathlib v4.35.0.
    - **Dependent declarations**: `theorem_7_5`.

26. **`berend_harmse_irreducible_factor`**
    - **Source**: D. Berend and J. E. Harmse, *Trans. Amer. Math. Soc.* 358 (2006), Theorem 1.1 ([5]).
    - **Statement**: If $P(x) \in \mathbb{Z}[x]$ has an irreducible factor over $\mathbb{Q}$ of degree $\ge 2$, then $n! = P(x)$ has only finitely many solutions.
    - **Justification**: Published external finiteness theorem cited directly in Theorem 7.5's $4 \mid k$ case.
    - **Dependent declarations**: `theorem_7_5`.

27. **`modularity_serre_ribet_package`**
    - **Source**: A. Wiles ([63]), C. Breuil, B. Conrad, F. Diamond, R. Taylor ([2]), B. Mazur ([39]), M. A. Kenku ([31]), J.-P. Serre ([51]), K. A. Ribet ([46]).
    - **Statement**: Coupled to `WeierstrassCurve ℚ`: any elliptic curve $E/\mathbb{Q}$ with full rational 2-torsion and non-integral $j$-invariant is modular, has surjective mod-$\ell$ image $\mathrm{GL}_2(\mathbb{F}_\ell)$ for all primes $\ell \ge 5$, and its Ribet lowered level $N_\ell$ retains every multiplicative prime $p$ with $\ell \nmid v_p(\Delta_{\min})$.
    - **Justification**: Modularity theorem, Mazur–Kenku isogeny bounds, Serre's open image theorem, and Ribet level-lowering are not in Mathlib v4.35.0.
    - **Dependent declarations**: `theorem_9_1_i`, `theorem_9_1_ii`, `prop_9_3_i`.

28. **`matveev_yu_linear_forms_bound`**
    - **Source**: E. M. Matveev ([38]), K. Yu ([64]).
    - **Statement**: Effective lower bound $\log |\sum_{i=1}^N b_i \log p_i| \ge -C^N N^N (\prod_{i=1}^N \log p_i) \log B$ for nonzero linear forms in logarithms of primes.
    - **Justification**: Baker–Matveev–Yu theorems on linear forms in logarithms are not in Mathlib v4.35.0.
    - **Dependent declarations**: `prop_9_3_ii`.
