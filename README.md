# FixedNumerator

Lean 4 / Mathlib formalization of the local step in extending Theorem 1.1 of C. David, A. Dunn,
A. Hamieh and H. Lin, *Quartic Gauss sums over primes and metaplectic theta functions*
(arXiv:2306.11875, to appear in Algebra & Number Theory), from the numerator `1` to any fixed
numerator `ν`.

Companion note: J. S. Farland, *Quartic Gauss sums over primes with a fixed numerator*
(preprint, Zenodo, 2026, [doi:10.5281/zenodo.23882882](https://doi.org/10.5281/zenodo.23882882)).

Archived on Zenodo: [doi:10.5281/zenodo.23882652](https://doi.org/10.5281/zenodo.23882652).

DDHL prove that `∑_{c ≡ β (4)} g̃₄(c) (c/|c|)^ℓ Λ(c) R(N(c)/X) ≪ X^{5/6+ε}`. The note shows that
their argument gives `X^{5/6+ε}(1 + |ℓ|)^{3/2+ε}` for `g̃₄(ν, c)` with any fixed nonzero `ν`. The
only new ingredient is a local identity that removes the primes dividing `ν` from the coprimality
conditions in the Type I Dirichlet series. This repository formalizes that step and the
bookkeeping around it:

- **DDHL (3.6)** from biquadratic reciprocity (3.2), the twist rule (3.4) and twisted
  multiplicativity (3.5) (`ddhl_3_6`).
- **The splitting identity**: for a primary `π` and a primary `c'` prime to `π`,
  `g₄(μ, π^k c') = (-1)^{C(c', π^k)} g₄(μ, π^k) g₄(μ π^{2k}, c')`, with no condition linking `μ` and
  `π` (`splitting_identity`). Also periodicity of the numerator modulo `π⁴`
  (`numerator_period`).
- **The 2-adic facts behind the signs**:
  - `π² ≡ 1 (mod 4)` for primary `π` (`primary_sq_mod_four`);
  - the sign depends only on the class modulo `4` (`sign_class_invariant`);
  - the sign is `1` at even powers (`sign_even_power`).
- **Lemma 2.2**: the splitting identity for the truncated series
  `∑_{N(c) ≤ X, c ≡ β (4), (c, γ) = 1} g₄(μ, c) W(c)`, as an exact finite identity
  (`lemma_2_2`).
- **Corollary 2.3**, removing `π` from the coprimality condition, for `μ = π^e μ'` with `μ'` prime
  to `π` and every `e ≥ 0`:
  - on the series prime to `π`, the valuation reduces modulo `4`: `π^e μ'` may be replaced by
    `π^{e mod 4} μ'` (`corollary_2_3_reduce`);
  - the splitting for every `e`, with all its terms: by the support of `g₄(μ, π^k)` (DDHL (3.7))
    they are `k = 4j ≤ e` and `k = e + 1` (`corollary_2_3_general`). For `e ≥ 4` there are more
    than two; at `e = 5` the terms are `k = 0, 4, 6`;
  - the four exact valuations `e = 0, 1, 2, 3`, to which the reduction brings every series prime
    to `π`: for `e = 1, 3` a single equation (`corollary_2_3_odd`) and its explicit finite inverse,
    the truncated `1/Δ(s)` (`corollary_2_3_odd_inverse`); for `e = 0, 2` the coupled pair of DDHL
    (8.6) and (8.7) (`corollary_2_3_coupled`). These single equations are stated for `e ≤ 3` only;
    they do not hold as written for `e ≥ 4`;
  - the determinants are bounded below on `Re s ≥ 1`: `determinant_lower`, `determinant_ne_zero`,
    `determinant_r1`, `determinant_r3`, `determinant_coupled`.

The passage from smoothed to sharp sums in the note's Corollary 1.2 is routine and is not among
the registered statements. A Lean proof of it remains in `FixedNumerator/Sharp.lean` as part of the
development, but it is not in `Challenge.lean` or `comparator.json`.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
scripts/verify-comparator.sh
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`. Comparator accepts `Solution` against `Challenge` under the Lean, NanoDa and
con-ron kernels. The structure `QuarticData` is compared as well: a modified copy in
`Challenge.lean` is rejected.

## Scope and what is cited

Mathlib has no quartic residue symbol, no quartic Gauss sum over `ℤ[i]` and no biquadratic
reciprocity. So the symbol `(r/c)₄` and the Gauss sum `g₄(μ, c)` are abstract functions, packaged
in `QuarticData` with the identities of DDHL §3 that the computation uses:
- multiplicativity of the symbol, and `χ⁴ = 1` on coprime pairs;
- biquadratic reciprocity (3.2);
- the twist rule (3.4);
- twisted multiplicativity (3.5);
- `g₄(μ, 1) = 1`;
- the support part of the local formula (3.7).

That the actual symbol and Gauss sum satisfy them is DDHL §3 and is not formalized. Dirichlet
series are replaced by their truncations at norm `X`, with a completely multiplicative weight `W`
standing for `(c/|c|)^ℓ N(c)^{-s}`. Numerators lie in `ℤ[i]`, which covers the numerators `-ib³`
and `-8ib³ = λ⁶b³` used in Paper VIII of the series.

Not formalized, and cited from DDHL in the note:
- the meromorphic continuation and convexity bounds of the metaplectic Dirichlet series
  (Proposition 4.3);
- Suzuki's relation (4.39);
- the quadratic large sieve;
- Vaughan's identity and the Type I and Type II estimates;
- the contour shift;
- Theorem 1.1 itself.

## Layout

- `FixedNumerator/Defs.lean`: definitions.
- `FixedNumerator/Primary.lean`: primary elements, norms modulo `8`, signs.
- `FixedNumerator/Local.lean`: (3.6), the splitting identity, periodicity.
- `FixedNumerator/Split.lean`: Lemma 2.2 for truncated sums.
- `FixedNumerator/Cases.lean`: Corollary 2.3 for `e = 0, 1, 2, 3` and the finite inverse.
- `FixedNumerator/General.lean`: Corollary 2.3 for every `e`: the reduction modulo `4` and the
  general splitting.
- `FixedNumerator/Determinant.lean`: the determinant bounds.
- `FixedNumerator/Sharp.lean`: the smoothing removal of Corollary 1.2 (not registered).
- `Challenge.lean` / `Solution.lean` / `comparator.json`: the Palomar statement surface.

## Changes

- **v1.1.** After the Palomar review of v1.0:
  - Corollary 2.3 now covers every valuation, not only `e = 0, 1, 2, 3`: new statements
    `corollary_2_3_reduce` (the valuation reduces modulo `4` on the series prime to `π`) and
    `corollary_2_3_general` (the splitting for every `e`, with its terms at `k = 4j ≤ e`). In v1.0
    the README described the cases by `ord_π μ` modulo `4`, while the single equations hold only
    for `e ≤ 3`.
  - The smoothing removal (`smoothing_removal`, Corollary 1.2) is no longer a registered statement,
    and the definitions `countAbs`, `sharpSum`, `smoothSum` it used are no longer compared.
  - The other 16 statements are unchanged.
