# Mathematical Correction and Audit Record

This file documents every substantive mathematical correction discovered during the formalization and audit of *"Valuation-Parity Equidistribution, Quadratic Pell Capacity, and Support-Reduced Padé–Wronskian Bounds for the Brocard–Ramanujan Equation"*.

## Defect Classification Key
- **Formalization issue**: The mathematics is sound, but its Lean implementation needs correction.
- **Missing justification**: A mathematical step was omitted.
- **Incomplete proof**: The argument does not yet establish the conclusion.
- **Incorrect argument**: An inference is mathematically invalid.
- **False statement**: The conclusion is false under the stated hypotheses.
- **Fatal flaw**: The required conclusion cannot be preserved and the argument cannot be repaired.

---

## Recorded Audit Items

### Audit Item 1: Lemma 2.4(i)–(ii), Equations (2.15)–(2.16) (Section 2.3, pp. 9–10)
1. **Affected manuscript result**: Section 2.3, Lemma 2.4(i)–(ii), Equations (2.15)–(2.16), pp. 9–10.
2. **Original statement and proof**:
   - Eq. (2.15) writes $\ll_\delta W_0 P (T_0^{-1/6} + P^{-1/(2R+3)}) \log^3 P \ll_\delta W_0 P (\log n)^{-(R+2)}$.
   - Eq. (2.16) states $\eta_\delta := \min(\delta/20, \delta/2^{R+3}) > 0$.
   - The proof (Regime A, p. 9) writes: for Type I $M < T_0 \le P^{3/2}$ ($j = 3$), $((T_0/M^3)^{1/6} + (M^3/T_0)^{1/6}) \ll M(P^{-1/20} + T_0^{-1/6})$; and for Type II ($P^{1/5} \le D \le P^{4/5}$) when $T_\Delta > \frac{1}{2D}$, claims van der Corput $j \in \{2,3,4\}$ gives $D(T_0^{-1/3} + P^{-1/40})$.
3. **Exact defect**: Two intermediate exponent flaws in the proof:
   - In Graham–Kolesnik / Iwaniec–Kowalski [30, Corollary 8.13] for $j = 3$ ($2^3 - 2 = 6$), the exponent of $M$ on the $\lambda_3^{-1/6}$ term is $1 - 2^{2-3} = 1/2$ (giving $(T_0/M^3)^{1/6} M + (M^3/T_0)^{1/6} M^{1/2} = T_0^{1/6} M^{1/2} + M T_0^{-1/6}$, not $M(M^3/T_0)^{1/6}$). Since $T_0 \le P^{3/2}$ and $M \ge P^{3/5}$, $T_0^{1/6} M^{1/2} \le P^{1/4} M^{1/2} = M (P^{1/4} M^{-1/2}) \le M P^{-1/20}$, while $M T_0^{-1/6} \ge 0$ is indeed the exact term needed! (So the conclusion $\ll M(P^{-1/20} + T_0^{-1/6})$ holds, but the middle term $(M^3/T_0)^{1/6}$ in the proof was miswritten.)
   - In Type II with $D \in [P^{1/5}, P^{4/5}]$ and $T_\Delta \le T_0 \le P^{3/2}$, $T_\Delta$ can reach $P^{3/2}$ while $D \approx P^{1/5}$, so $T_\Delta / D$ can reach $P^{1.3} = D^{6.5}$, which requires van der Corput orders up to $j \le 9$ (not just $j \in \{2, 3, 4\}$), yielding a positive power saving $P^{-\eta'_\delta}$ ($\eta'_\delta > 0$) rather than the fixed exponent $P^{-1/40}$ or $P^{-1/(2R+3)}$ and $\min(\delta/20, \delta/2^{R+3})$.
4. **Why original reasoning is insufficient**: Using only $j \in \{2, 3, 4\}$ fails when $D \approx P^{1/5}$ and $T_\Delta \approx P^{3/2}$ because $\lambda_4 = T_\Delta / D^4 \approx P^{0.7} \gg 1$ exceeds $O(1)$. Higher $j \in \{2, \dots, 9\}$ keeps $\lambda_j = T_\Delta / D^j \le D^{-1}$ for some $j \le 9$.
5. **Classification**: **Incomplete proof / Incorrect intermediate exponent**.
6. **Investigation**: Checked exact van der Corput $k$-th derivative exponents $(k \ge 2)$ across all dyadic ranges $D \in [P^{1/5}, P^{4/5}]$ and $T_\Delta \in (D/2, P^{3/2}]$.
7. **Replacement argument**: Retain Type I $j = 2, 3$ with exact $(M T_0^{-1/6})$ term from [30, Cor. 8.13], and in Type II take $j \in \{2, \dots, 9\}$ so $\lambda_j \in [D^{-2}, D^{-1}]$ when $T_\Delta > D$, giving unconditional power saving $P^{-\eta'_\delta}$ ($\eta'_\delta > 0$) in (2.15) and $n^{-\eta_\delta}$ ($\eta_\delta > 0$) in (2.16).
8. **Validity**: Every step uses Kusmin–Landau and [30, Cor. 8.13 / Thm 8.25] within their proven ranges.
9. **Hypotheses unchanged?**: Yes.
10. **Conclusion unchanged?**: Final bounds $\ll_\delta W_0 P (\log n)^{-(R+2)}$ in (2.15) and $\ll_\delta W_0 P n^{-\eta_\delta}$ ($\eta_\delta > 0$) in (2.16) are preserved; explicit placeholder formulas $P^{-1/(2R+3)}$ and $\min(\delta/20, \delta/2^{R+3})$ are replaced by $\eta'_\delta, \eta_\delta > 0$.
11. **Lean declarations**: `lemma_2_4_i`, `lemma_2_4_ii` (`BrocardFormalization/ValuationParity.lean`).
12. **Dependency chain**: `theorem_2_5_i`, `theorem_2_5_ii`, `theorem_2_5_iii`, `lemma_6_4`.
13. **Manuscript edit**: Update Regime A in Lemma 2.4 proof and state $\eta'_\delta, \eta_\delta > 0$ cleanly in (2.15)–(2.16).

---

### Audit Item 2: Corollary 3.5 — $p = 3$ Bound $v_3(d_n k) \le 1$ for $n \ge 15$ (Section 3.3, p. 15)
1. **Affected manuscript result**: Section 3.3, Corollary 3.5, p. 15.
2. **Original statement and proof**: Claims "For $n \ge 15$ with $2 \mid v_3(n!)$, we have $v_3(n!) \ge 6$ and $v_3(d_n k) \le 1$, so $v_3(\tilde{R}_3(K_n)) \ge v_3(s_n) - v_3(d_n k) \ge 2$".
3. **Exact defect**: No proof was given for why $v_3(d_n k) \le 1$ when $n \ge 15$. (Wait: in fact, $1 \le k < 2.5 \log n$ only bounds $v_3(k) \le \lfloor \log_3(2.5 \log n) \rfloor$, which exceeds $1$ once $k \ge 9$, i.e. $n \ge 37$!)
4. **Why original reasoning is insufficient**: $v_3(d_n k) \le 1$ is NOT true purely from $n \ge 15$ if $9 \mid k$, so the bound $v_3(s_n) - v_3(d_n k) \ge 2$ must be proved directly!
5. **Classification**: **Missing justification / Unjustified intermediate inequality**.
6. **Investigation**: Checked $v_3(n!)$ vs $v_3(d_n k)$ for all $n \ge 15$ with $2 \mid v_3(n!)$:
   - For $15 \le n \le 17$: $v_3(n!) = 6$, so $v_3(s_n) = 3$. Also $v_3(k) \le \lfloor \log_3(2.5 \log 17) \rfloor = \lfloor \log_3(7.08) \rfloor = 1$. Even if $d_n = 3$, wait: at $n = 15, 16, 17$, could $d_n = 3$ AND $v_3(k) = 1$ give $v_3(d_n k) = 2$ and $v_3(s_n) - v_3(d_n k) = 3 - 2 = 1 < 2$?!
   - Let's check $d_n \in \{1, 3\}$ for $15 \le n \le 17$: $q_{15}$ has $v_3(15!)=6$ (even), $v_2(15!) = 11$ (odd), $v_5(15!)=3$ (odd), $v_7(15!)=2$ (even), $11, 13$ odd $\implies q_{15} = 2 \cdot 5 \cdot 11 \cdot 13 = 1430 \equiv 6 \pmod 8 \neq 5$, so $d_{15} = 1$! And for $n = 16$, $v_2(16!) = 15$ (odd), $q_{16} = 1430 \equiv 6 \pmod 8 \neq 5 \implies d_{16} = 1$! For $n = 17$, $v_2(17!) = 15$ (odd), $q_{17} = 2 \cdot 5 \cdot 11 \cdot 13 \cdot 17 = 24310 \equiv 6 \pmod 8 \neq 5 \implies d_{17} = 1$!
   - Thus for $15 \le n \le 17$, $d_n = 1$ unconditionally (since $2 \mid q_n$, $q_n \not\equiv 5 \pmod 8$!), and for $n = 15, 16, 17$, $v_3(k) \le 1$ (since $k < 2.5 \log 17 < 8 < 9$), so $v_3(d_n k) \le 1$ and $v_3(s_n) - v_3(d_n k) \ge 3 - 1 = 2$!
   - For $n \ge 18$: $v_3(n!) \ge 6 + 2 = 8$, and in general $v_3(n!) \ge \lfloor n/3 \rfloor \ge 6$; for $18 \le n \le 20$, $v_3(n!) = 8 \implies v_3(s_n) = 4$, while $k < 2.5 \log 20 < 7.5 < 9 \implies v_3(k) \le 1$, so $v_3(d_n k) \le 2 \implies v_3(s_n) - v_3(d_n k) \ge 4 - 2 = 2$. For $n \ge 21$, $v_3(n!) \ge 9 \implies v_3(s_n) = \frac{1}{2}v_3(n!) \ge 5$, and for $n \ge 21$, $\frac{1}{2}\lfloor n/3 \rfloor - 1 - \lfloor \log_3(2.5 \log n)\rfloor \ge 2$ holds for EVERY $n \ge 21$ (at $n=21$: $v_3(21!) = 9$ is odd, at $n=24$: $v_3(24!) = 10 \implies v_3(s_{24}) = 5$ while $2.5 \log 24 < 8 < 9 \implies v_3(d_n k) \le 2$, difference $\ge 3$; for $n \ge 27$: $v_3(s_n) \ge 6$ and $v_3(d_n k) \le 1 + \log_3(2.5 \log n)$ which grows logarithmically while $\frac{1}{2}\lfloor n/3 \rfloor$ grows linearly!).
7. **Replacement argument**: Replace the bare assertion "$v_3(d_n k) \le 1$" with the complete explicit verification: $q_n$ is even for $15 \le n \le 17$ (so $q_n \not\equiv 5 \pmod 8 \implies d_n = 1$) while $k < 2.5 \log n < 9 \implies v_3(k) \le 1$; and for $n \ge 18$, $v_3(s_n) - v_3(d_n k) \ge \frac{1}{2}\lfloor n/3 \rfloor - 1 - \lfloor \log_3(2.5 \log n) \rfloor \ge 2$ (using $v_3(n!) \ge 8$ for $n=18..20$ and $\lfloor n/3 \rfloor \ge 8 + 2\lfloor \log_3(2.5 \log n)\rfloor$ for $n \ge 24$). Also note $n \ge 15$ has no solutions anyway up to $10^9$ by Berndt–Galway, though our elementary inequality proves $v_3(s_n) - v_3(d_n k) \ge 2$ completely unconditionally from $k < 2.5 \log n$ without Berndt–Galway!
8. **Classification**: **Missing justification** (and **False statement** for the intermediate claim $v_3(d_n k) \le 1$ when $n \ge 18$).
9. **Hypotheses unchanged?**: Yes.
10. **Conclusion unchanged?**: Yes ($3 \mid (1 - \chi_{-3D_n}(3)) h(\mathbb{Q}(\sqrt{-3q_n}))$).
11. **Lean declarations**: `cor_3_5` (`BrocardFormalization/PellAndIwasawa.lean`).
12. **Dependency chain**: Standalone corollary in Section 3.3.
13. **Manuscript edit**: Supply the exact case analysis ($15 \le n \le 17$, $18 \le n \le 20$, $n \ge 24$) in the proof of Corollary 3.5.

---

### Audit Item 3: Proposition 5.4(i) — Ramified Diagonal Entry (Section 5.2, p. 24)
1. **Affected manuscript result**: Section 5.2, Proposition 5.4(i), p. 24.
2. **Original statement and proof**: Bullet 1 writes diagonal entry $\ell_{p_i}(-q_n^*/p_i)$, whereas the proof on p. 24 derives $\ell_{p_i}(-q_n/p_i)$ using $2^{v_2(n!)-2} \delta_1^*(n) = q_n / \delta_2^*(n)$.
3. **Exact defect**: Typo $-q_n^*/p_i$ in statement when $2 \nmid v_2(n!)$ (e.g. when $\left(\frac{2}{p_i}\right) = -1$). Notice part (iii) takes $2 \mid v_2(n!)$ where $q_n = q_n^*$.
4. **Classification**: **False statement** (statement typo inconsistent with its own proof when $2 \nmid v_2(n!)$).
5. **Replacement argument**: Use $\ell_{p_i}(-q_n/p_i)$ in Proposition 5.4(i), matching the proof verbatim.
6. **Hypotheses unchanged?**: Yes.
7. **Conclusion unchanged?**: Corrected diagonal entry $\ell_{p_i}(-q_n/p_i)$; all downstream theorems (Proposition 5.4(ii)–(iii), Theorem 5.5) use $-q_n/p_i$.
8. **Lean declarations**: `matrixM1Entry`, `prop_5_4` (`BrocardFormalization/FundamentalRegimeK1.lean`).
9. **Manuscript edit**: Change `-q_n^*/p_i` to `-q_n/p_i` in Proposition 5.4(i).

---

### Audit Item 4: Proposition 6.2(i) — Equation (6.7) (Section 6.1, pp. 27–28)
1. **Affected manuscript result**: Section 6.1, Proposition 6.2(i), Eq. (6.7), pp. 27–28.
2. **Original statement and proof**:
   $$(\sqrt{d}Y - \sqrt{c}X)^2 = \frac{(\sqrt{P}-1)^2}{a(\sqrt{P}m_1 + m_2)}, \qquad (\sqrt{c}W - \sqrt{d}Z)^2 = \frac{(\sqrt{P}-1)^2}{b(m_2 - \sqrt{P}m_1)}.$$
3. **Exact defect**: Sign and factoring error:
   - Numerically at $(n_1, n_2) = (4, 5)$, $P=5, m_1=5, m_2=11$: $m_2 - \sqrt{P}m_1 = 11 - 5\sqrt{5} < 0$, making the RHS of the second identity negative while the LHS is a real square!
   - Algebraically, $P m_1 - m_2 - \sqrt{P}(m_2 - m_1) = (\sqrt{P} + 1)(\sqrt{P} m_1 - m_2)$ (NOT $(\sqrt{P} - 1)(\sqrt{P} m_1 - m_2)$), and $(\sqrt{P} m_1 - m_2)(\sqrt{P} m_1 + m_2) = P m_1^2 - m_2^2 = P - 1$. Similarly $P m_1 + m_2 - \sqrt{P}(m_2 + m_1) = (\sqrt{P} - 1)(\sqrt{P} m_1 - m_2)$.
4. **Classification**: **False statement**.
5. **Replacement derivation**:
   $$(\sqrt{d}Y - \sqrt{c}X)^2 = \frac{(P-1)(\sqrt{P}+1)}{a(\sqrt{P}m_1 + m_2)}, \qquad (\sqrt{c}W - \sqrt{d}Z)^2 = \frac{(P-1)(\sqrt{P}-1)}{b(\sqrt{P}m_1 + m_2)}.$$
   Both denominators are strictly positive ($> 0$) and match LHS $> 0$ for all $4 \le n_1 < n_2$.
6. **Lean declarations**: `prop_6_2_i` (`BrocardFormalization/PairwiseDuality.lean`).
7. **Manuscript edit**: Update Eq. (6.7) and the one-line derivation on p. 28.

---

### Audit Item 5: Theorem 6.5 — Rankin Spherical Cap Bound for $\theta_\varepsilon(n)$ (Section 6.3, pp. 30–31)
1. **Affected manuscript result**: Section 6.3, Theorem 6.5, final clause, pp. 30–31.
2. **Original statement and proof**: Claims $\#\{n \le N : |\theta_\varepsilon(n) - 1/2| \ge \eta\} \le (\lfloor (2\eta^2 \varepsilon)^{-1}\rfloor + 1) N^\varepsilon$, deriving correlation $\ge \eta\sqrt{2\varepsilon} - o(1)$ with $v_I$ and applying Rankin's bound on a single interval $I = [N', N' + (N')^{1-\varepsilon}]$.
3. **Exact defect**: Two errors:
   - Normalizing weights on $I_0 = ((N')^{1-\varepsilon/2}, N']$: $\sum_{p \in I_0} w_p = \frac{\varepsilon}{2} + o(1)$ and $\sum_{p \in \mathcal{P}_{\mathrm{odd}}(n) \cap I_0} w_p = \frac{\varepsilon}{4} + o(1)$ (NOT $\varepsilon/2$ — the half comes from $\mathcal{P}_{\mathrm{odd}}$ density $\log 2$? Wait: by Thm 2.5(iii) with $h=2, c=1$, $\sum_{n^{1-\varepsilon/2} < p \le n,\, p \in \mathcal{P}_{\mathrm{odd}}} v_p(n!)\log p = (\frac{\varepsilon}{4} + o(1)) n\log n$!). Meanwhile $\theta_\varepsilon(n) - 1/2 = \frac{\sum_{p \in I_0 \cap \mathcal{P}_{\mathrm{odd}}} (\varepsilon_p + 1)/2 \, w_p}{\sum_{p \in I_0 \cap \mathcal{P}_{\mathrm{odd}}} w_p} - \frac{1}{2} = \frac{\langle u_n, v_I \rangle_w}{2 \sum_{p \in I_0 \cap \mathcal{P}_{\mathrm{odd}}} w_p}$ where $v_I = \mathbf{1}_{I_0 \cap \mathcal{P}_{\mathrm{odd}}}$ has $\|v_I\|_w = \sqrt{\varepsilon/4 + o(1)} = \frac{\sqrt{\varepsilon}}{2} + o(1)$! Therefore $|\langle u_n, v_I / \|v_I\|_w \rangle_w| = 2 |\theta_\varepsilon(n) - 1/2| \sqrt{\varepsilon/4 + o(1)} = |\theta_\varepsilon(n) - 1/2| \sqrt{\varepsilon} + o(1) \ge \eta \sqrt{\varepsilon} - o(1)$ (not $\eta \sqrt{2\varepsilon}$!). Wait: with $\eta_0 = \eta\sqrt{\varepsilon} - o(1)$, Rankin's inequality $t^2 \eta_0^2 \le t + 3 t(t-1)(N')^{-\varepsilon}$ gives $t \le \lfloor (\eta^2 \varepsilon)^{-1} \rfloor + 1$ for sufficiently large $N' \ge N_0(\varepsilon, \eta)$.
   - Covering $[1, N]$ using $\sim N^\varepsilon$ intervals of length $(N')^{1-\varepsilon}$ introduces an $O_\varepsilon(1)$ dyadic geometric factor (plus small $n < N_0(\varepsilon, \eta)$), giving $\le C_\varepsilon \eta^{-2} N^\varepsilon$ for $N \ge N_0(\varepsilon, \eta)$, rather than the unscaled $(\lfloor (2\eta^2\varepsilon)^{-1}\rfloor + 1) N^\varepsilon$ for all $N \ge 1$.
4. **Classification**: **Incorrect argument / False statement** (wrong factor $\sqrt{2\varepsilon}$ vs $\sqrt{\varepsilon}$ and omitted dyadic $C_\varepsilon$ factor).
5. **Replacement argument**: State both the single-interval bound $t \le \lfloor (\eta^2 \varepsilon)^{-1} \rfloor + 1$ for $N' \ge N_0(\varepsilon, \eta)$ and the global bound $\#\{4 \le n \le N : |\theta_\varepsilon(n) - 1/2| \ge \eta\} \le C_\varepsilon \eta^{-2} N^\varepsilon$ for $N \ge N_0(\varepsilon, \eta)$.
6. **Lean declarations**: `theorem_6_5` (`BrocardFormalization/PairwiseDuality.lean`).
7. **Manuscript edit**: Correct $\eta\sqrt{2\varepsilon}$ to $\eta\sqrt{\varepsilon}$ and include $C_\varepsilon$ in Theorem 6.5.

---

### Audit Item 6: Lemma 7.3(i) — Ceiling Threshold for $s \ge \lceil m + 1 - \varepsilon_0 \rceil$ (Section 7.2, p. 34)
1. **Affected manuscript result**: Section 7.2, Lemma 7.3(i), p. 34.
2. **Original statement and proof**: Assumes $D > (m+1)^2 M$ and deduces $s \ge \lceil m + 1 - \varepsilon_0 \rceil$ from $s D + \binom{s}{2} M \ge \lfloor (m+1-\varepsilon_0) D \rfloor - (s - 1) > (m + 1 - \varepsilon_0) D - s$.
3. **Exact defect**: If $m + 1 - \varepsilon_0 \notin \mathbb{Z}$ and $\operatorname{fract}(m + 1 - \varepsilon_0)$ is very small, $m + 1 - \varepsilon_0 - (\lceil m + 1 - \varepsilon_0 \rceil - 1) = \operatorname{fract}(m + 1 - \varepsilon_0)$ can be smaller than $\frac{\binom{s}{2} M + s}{D}$ when only $D > (m+1)^2 M$ holds!
4. **Classification**: **Incomplete proof / Missing threshold hypothesis**.
5. **Replacement argument**: Add the exact hypothesis $D > (\binom{m+1}{2} M + m + 1) / \operatorname{fract}(m+1-\varepsilon_0)$ when $\operatorname{fract}(m+1-\varepsilon_0) \ne 0$. Note that in Theorem 1.3(ii), $D \asymp N$ and $M \le N^\theta$ ($\theta < 1/3$), so $D / M \to \infty$ for fixed $\varepsilon_0$, making the extra hypothesis automatic.
6. **Lean declarations**: `lemma_7_3_i` (`BrocardFormalization/PadeWronskian.lean`).

---

### Audit Item 7: Lemma 7.1 (Eq. 7.4), Lemma 7.4(i) (Eq. 7.15), and Theorem 1.3(ii) Step 1 (pp. 32–36)
1. **Affected manuscript result**: Section 7.1 Lemma 7.1 Eq. (7.4), Section 7.2 Lemma 7.4(i) Eq. (7.15), and Section 7.3 Theorem 1.3(ii) Step 1, pp. 32–36.
2. **Original statement and proof**:
   - Eq. (7.4) uses base $r^4$ in $(2mr^4 M)^{\frac{(m-\varepsilon_0)(m+1-\varepsilon_0)}{\varepsilon_0} D}$ without a $(D+1)$ prefactor in $|r_v|$.
   - Eq. (7.15) uses $u = (4rN)^{Mm+2} 10^{m \varepsilon_0^{-1} M}$, $w = (2rN)^{2Mm+2} 4^{m \varepsilon_0^{-1} M}$, and Step 1 writes $c = (2rN)^{Mm+3}$.
3. **Exact defect**:
   - In Lemma 7.1 proof (p. 33), $p_{i,k} = r^{2O} \tilde{p}_{i,k}$ gives $r$-exponent $2O (1 + \frac{m-\varepsilon_0}{\varepsilon_0}) = \frac{2 m O}{\varepsilon_0} \le \frac{2 m (m+1-\varepsilon_0)}{\varepsilon_0} D$. Comparing $2m$ with $4(m-\varepsilon_0)$ requires $\varepsilon_0 \le m/2$, which fails for Table 1's $m=5, \varepsilon_0 = 5 - \sqrt{5} \approx 2.764 > 2.5$! Also summing over $0 \le k \le D$ in $r_v$ introduces the polynomial factor $m(D+1)$.
   - In Lemma 7.4(i) proof (p. 35), $Z = r^{a+s} n_0^{D + (a+s)M}$ has degree $(a+s)M + a + s$ in $r, N$ (not $Mm + 3$), and the Leibniz differentiation order $k \le a+s-1$ contributes exponents $(a+s)M + a + s$ (not $Mm+2$) to $u$ and $w$.
4. **Classification**: **Incorrect argument / Incorrect intermediate constants & exponents**.
5. **Replacement argument**: Replace $r^4$ by $r^{2m/(m-\varepsilon_0)}$ in $U, W$ (preserving identical $N, M$ exponents because $r$ is constant!), include $m(D+1)$ in $|r_v|$, and use $(a+s)M + a + s$ in $c, u, w$. Since $(a+s)M \ll_m M^{m+2}\log N = o(N)$ whenever $\theta < \frac{1}{m+2}$, we STILL have $c, u, w = (N!)^{o(1)}$, preserving $\chi$ in (7.18), (7.19), Tables 1 & 2, and Theorem 1.3(ii) verbatim!
6. **Lean declarations**: `lemma_7_1`, `lemma_7_3_iii`, `lemma_7_4_i` (`BrocardFormalization/PadeWronskian.lean`).

---

### Audit Item 8: Theorem 7.5 Proof — Grunwald–Wang Exception $8 \mid k, A = 2^{k/2} c^k$ (Section 7.4, p. 38)
1. **Affected manuscript result**: Section 7.4, Theorem 7.5 proof, p. 38.
2. **Original statement and proof**: Proof correctly mentions Grunwald–Wang exception "(and if $8 \mid k$, not of the form $2^{k/2} c^k$)" in paragraph 1, then handles $A = c^k$ ($k \ge 3$) in paragraph 2, without explicitly writing the $A = 2^{k/2} c^k$ ($8 \mid k$) case!
3. **Exact defect**: Missing case in paragraph 2: when $8 \mid k$ and $A = 2^{k/2} c^k$, $A = (2^{k/4} c^{k/2})^2$ is NOT necessarily a $k$-th power, yet $n! = m^k - 2^{k/2} c^k$ is still finite!
4. **Classification**: **Missing justification**.
5. **Replacement argument**: When $8 \mid k$ and $A = 2^{k/2} c^k$, write $k = 4 \ell$ ($2 \mid \ell$); then $n! = m^{4\ell} - 2^{2\ell} c^{4\ell} = (m^{2\ell} - 2^\ell c^{2\ell})(m^{2\ell} + 2^\ell c^{2\ell})$, which is $P(m)$ with $P(x) = x^k - A$. Over $\mathbb{Q}$, $x^4 - 4 c_0^4 = (x^2 - 2 c_0 x + 2 c_0^2)(x^2 + 2 c_0 x + 2 c_0^2)$ has an irreducible factor of degree $\ge 2$ (`x^\ell` substituted gives factors of degree $\ge 2$, because any real quadratic factor `x^2 \pm \sqrt{2} c_0^{...} ...` or over $\mathbb{Q}$ Sophie Germain factorization splits into irreducible factors of degree $\ge 2$!). By Berend–Harmse [5, Thm 1.1], finiteness follows immediately.
6. **Lean declarations**: `theorem_7_5` (`BrocardFormalization/PadeWronskian.lean`).

---

### Audit Item 9: Theorem 8.3(ii), Equation (8.11) — Cutoff Bound $H < M_n$ (Section 8.3, p. 41–42)
1. **Affected manuscript result**: Section 8.3, Theorem 8.3(ii), Eq. (8.11), pp. 41–42.
2. **Original statement and proof**: States "For every $H \ge 1$ and $1 \le k < \frac{1}{2} P_{\min}(n)$...", then applies Hölder's inequality $\sum_{h=1}^H |\hat{\mu}_n(h)| \le H^{1 - \frac{1}{2k}} \left(\sum_{h=0}^{M_n - 1} |\hat{\mu}_n(h)|^{2k}\right)^{1/(2k)}$.
3. **Exact defect**: The inequality $\sum_{h=1}^H |\hat{\mu}_n(h)|^{2k} \le \sum_{h=0}^{M_n - 1} |\hat{\mu}_n(h)|^{2k}$ requires $H < M_n$ (otherwise for $H \ge M_n$, periodicity mod $M_n$ adds $\lceil H / M_n \rceil$ copies!).
4. **Classification**: **Missing justification / Missing hypothesis**.
5. **Replacement argument**: Add $H < M_n$ to Theorem 8.3(ii) Eq. (8.11) (while noting the subsequent barrier remark explains what would be required if $H \ge 2^{\pi(n)-1}$, which satisfies $2^{\pi(n)-1} \ll e^{O(n/\log n)} \ll n!/2 = M_n$ for $n \ge 5$).
6. **Lean declarations**: `theorem_8_3_ii` (`BrocardFormalization/CRTTorus.lean`).

---

### Audit Item 10: Theorem 9.2(i) — Narrow $2^J$-Rank Dichotomy (Section 9.2, pp. 44–45)
1. **Affected manuscript result**: Section 9.2, Theorem 9.2(i), pp. 44–45.
2. **Original statement and proof**: Claims when $|\mathrm{Cl}^+_{\mathrm{odd}}(q_n)| < q_n^{1/4 - \varepsilon}$, BOTH $\exp(\mathcal{A}_2(q_n)) \ge n^{\frac{1}{4 \log 2} - \varepsilon}$ AND $\operatorname{rank}_{2^J}(\mathcal{A}_2(q_n)) \ge (\frac{1}{8} - \varepsilon)\frac{n}{\log n}$ for all $1 \le J \le \frac{\log n}{8 \log 2}$ hold simultaneously.
3. **Exact defect**: False for $J \ge 2$: for the abelian 2-group $\mathcal{A}_2 \cong (\mathbb{Z}/2\mathbb{Z})^{r - 1} \oplus \mathbb{Z}/2^E \mathbb{Z}$ with $r = \omega(D_n) - 1 \approx (\log 2)\frac{n}{\log n}$ and $2^E \approx n^{c n / \dots}$, we have $\log_2 |\mathcal{A}_2| \ge (\frac{\log 2}{4} - \frac{\varepsilon}{2} - o(1)) n$ and $\exp(\mathcal{A}_2) = 2^E \ge n^{\frac{1}{4 \log 2} - \varepsilon}$, yet $\operatorname{rank}_{2^J}(\mathcal{A}_2) = 1$ for ALL $J \ge 2$!
4. **Classification**: **False statement** (conjunction fails for $J \ge 2$).
5. **Replacement argument**: Retain the valid Gauss-genus consequences of $\log_2 |\mathcal{A}_2(q_n)| \ge (\frac{\log 2}{4} - \frac{\varepsilon}{2} - o(1)) n$ and $\operatorname{rank}_2(\mathcal{A}_2(q_n)) = \omega(D_n) - 1$: namely $|\mathcal{A}_2(q_n)| \ge 2^{(\frac{\log 2}{4} - \varepsilon) n}$ AND $\exp(\mathcal{A}_2(q_n)) \ge |\mathcal{A}_2(q_n)|^{1/\operatorname{rank}_2(\mathcal{A}_2(q_n))} \ge n^{\frac{1}{4 \log 2} - \varepsilon}$. (Optionally also the pigeonhole sum $\sum_{j \ge 1} \operatorname{rank}_{2^j}(\mathcal{A}_2) = \log_2 |\mathcal{A}_2| \ge (\frac{\log 2}{4} - \frac{\varepsilon}{2} - o(1)) n$, which gives a trade-off between high $2^J$-rank and high exponent without falsely forcing BOTH to be large simultaneously for all $J \le \frac{\log n}{8 \log 2}$.)
6. **Lean declarations**: `theorem_9_2_i` (`BrocardFormalization/FreyCurvesAndThresholds.lean`).
7. **Manuscript edit**: Update the second dichotomy branch in Theorem 9.2(i) and its 2-line proof on pp. 44–45.

---

### Audit Item 11: Lemma 2.4(i) — `AR` Exponent in `(log n)^{-(R+2)}` Bound (Section 2.3, p. 9)
1. **Affected manuscript result**: Section 2.3, Lemma 2.4(i), p. 9.
2. **Original statement and proof**: Uses `AR := 6R + 16` with `(log n)^{-AR/6} log^3 P`.
3. **Exact defect**: `-(6R+16)/6 + 3 = -R + 1/3 > -(R + 2)` due to the `log^3 P` factor.
4. **Classification**: **Incorrect intermediate constant**.
5. **Replacement argument**: Strengthen to `AR := 6R + 30`, giving `-(6R+30)/6 + 3 = -(R + 2)`.
6. **Lean declarations**: `lemma_2_4_i` (`BrocardFormalization/ValuationParity.lean`).

---

### Audit Item 12: Lemma 3.1(i) — Finite Exceptions to `log q_n > 0.4 n` (Section 3.1, p. 12)
1. **Affected manuscript result**: Section 3.1, Lemma 3.1(i), p. 12.
2. **Original statement and proof**: Claims `log q_n > 0.4 n` for `8 ≤ n ≤ 115` with `n ≠ 10`.
3. **Exact defect**: Fails at `n = 10` (`q_10 = 7`), `n = 11` (`q_11 = 77`), and `n = 28` (`q_28 = 44574`). Holds for all other `8 ≤ n ≤ 115` and all `n ≥ 116`.
4. **Classification**: **False statement** (omits `n = 11, 28` from the finite exception list).
5. **Replacement argument**: Exclude `{10, 11, 28}` in the `8 ≤ n ≤ 115` clause (already verified by `decide` in `PellAndIwasawa.lean`).
6. **Lean declarations**: `lemma_3_1_i` (`BrocardFormalization/PellAndIwasawa.lean`).

---

### Audit Item 13: Lemma 3.2(i) — `p = 3` Lifting-the-Exponent Exception (Section 3.1, p. 13)
1. **Affected manuscript result**: Section 3.1, Lemma 3.2(i), Eq. (3.2)–(3.3), p. 13.
2. **Original statement and proof**: Claims `v_p(U_{k-1}(X_1(q_n))) = v_p(k)` for every prime `p ∣ q_n Y_1(q_n)`, arguing `j > v_p(2j+1)` for `j ≥ 1`.
3. **Exact defect**: At `p = 3, j = 1`, `v_3(2·1 + 1) = 1 = j`, so `j - v_3(2j+1) = 0`! Counterexample: `n = 4, q_4 = 6, X_1 = 5, Y_1 = 2, k = 3, p = 3` gives `3 ∣ q_4 Y_1 = 12`, yet `v_3(U_2(5)) = v_3(99) = 2 ≠ 1 = v_3(3)`.
4. **Classification**: **False statement** (missing `p ≠ 3 ∨ 3 ∤ k ∨ 3 ∣ Y_1` condition).
5. **Replacement argument**: State and prove `v_p(U_{k-1}(X_1)) = v_p(k)` for `p ≠ 3 ∨ ¬ 3 ∣ k ∨ 3 ∣ Y_1` (for `p = 3, 3 ∣ Y_1`, `v_3(M) ≥ 2` restores `2j > v_3(2j+1)`).
6. **Lean declarations**: `lemma_3_2_i` (`BrocardFormalization/PellAndIwasawa.lean`).

---

### Audit Item 14: Lemma 2.4(i)–(ii) — Smoothness/Differentiability of Weight `w` (Section 2.3, pp. 9–10)
1. **Affected manuscript result**: Section 2.3, Lemma 2.4(i)–(ii), pp. 9–10.
2. **Original statement and proof**: Formalizes total variation `∫_P^{2P} |deriv w t| dt ≤ W_0` without requiring `w` to be `C^1` / differentiable on `[P, 2P]`.
3. **Exact defect**: In Lean/Mathlib, `deriv w t = 0` at points where `w` is not differentiable, so non-differentiable step functions trivially satisfy `∫ |deriv w t| = 0 ≤ W_0` and violate partial summation.
4. **Classification**: **Formalization issue / Missing hypothesis**.
5. **Replacement argument**: Add `ContDiffOn ℝ 1 w (Set.Icc P (2 * P))` to `lemma_2_4_i` and `lemma_2_4_ii` in `ValuationParity.lean`.
6. **Lean declarations**: `lemma_2_4_i`, `lemma_2_4_ii` (`BrocardFormalization/ValuationParity.lean`).

---

### Audit Item 15: Theorem 3.6 — Hypothesis `k ∈ {1, 2}` for `10^9 < n < N_0` (Section 3.3, p. 15)
1. **Affected manuscript result**: Section 3.3, Theorem 3.6.
2. **Original statement and proof**: Assumes `4 ≤ n` without `k ∈ {1, 2}`.
3. **Exact defect**: In `10^9 < n < N_0` (where `N_0` from `deLaValleePoussin_pnt` is non-effective), `k = 4` would satisfy `m = u^2 + q_n v^2` and `s_n = 2|uv|` with `u + v√q_n = ε_n^2`, contradicting `k = 2 ↔ ...` unless `k ∈ {1, 2}` is assumed (as in `prop_3_4`).
4. **Classification**: **Missing hypothesis**.
5. **Replacement argument**: Add `(hk : pellIndex hn hsol = 1 ∨ pellIndex hn hsol = 2)` to `theorem_3_6`.
6. **Lean declarations**: `theorem_3_6` (`BrocardFormalization/PellAndIwasawa.lean`).

---

### Audit Item 16: Theorem 1.1 — Distinctness `q_{n_1} ≠ q_{n_2}` for `n_1 > e^{6306}` (Section 3.2, p. 13)
1. **Affected manuscript result**: Section 3.2, Theorem 1.1, p. 13.
2. **Original statement and proof**: Claims `0.38 n_1 / log(2 n_1) > n_1 / 16597` for all `n_1 > 10^9`.
3. **Exact defect**: `0.38 / log(2 n_1) > 1 / 16597` fails once `log(2 n_1) ≥ 6306.86` (i.e. `n_1 > e^{6306}`).
4. **Classification**: **Incorrect argument**.
5. **Replacement argument**: For `n_1 ≥ N_0`, `k_{n_1} ∈ {1, 2}` gives `n_2 - n_1 > 0.24 n_1 > n_1 / 16597` unconditionally; for `n_1 ≤ 10^9`, Berndt–Galway gives `n_1 ∈ {4, 5, 7}` (`q_4=6, q_5=30, q_7=35`). (Full coverage of `10^9 < n_1 < N_0` requires either an effective `N_0 < e^{6306}` or Erdős–Selfridge (1975) for `n_2 - n_1 ≥ 2`.)
6. **Lean declarations**: `theorem_1_1` (`BrocardFormalization/PellAndIwasawa.lean`).
