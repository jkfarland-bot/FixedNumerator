module

public import Mathlib

public section

/-!
# Quartic Gauss sums with a fixed numerator: statements

This file is the statement surface for the Palomar registry. It restates, with their exact
library definitions, the objects the results are about, and states each result with `sorry`.
`Solution.lean` proves every statement below with the same name and type, using the development
in `FixedNumerator/`.

The quartic residue symbol `(r/c)₄` and the quartic Gauss sum `g₄(μ, c)` are abstract functions,
packaged in `QuarticData` with the identities of David, Dunn, Hamieh and Lin §3 that the local
computation uses ((3.2), (3.4), (3.5), `g₄(μ, 1) = 1` and the support part of (3.7)). That the
actual symbol and Gauss sum satisfy them is DDHL §3 and is not formalized. The analytic inputs of
DDHL (Proposition 4.3, Suzuki's relation (4.39), the quadratic large sieve, Vaughan's identity and
the contour shift) are not formalized either.

* `ddhl_3_6`: DDHL (3.6), derived from (3.2), (3.4), (3.5).
* `splitting_identity`: `g₄(μ, π^k c') = (-1)^{C(c', π^k)} g₄(μ, π^k) g₄(μ π^{2k}, c')`.
* `numerator_period`: `g₄(μ π^{4j}, c) = g₄(μ, c)` for `c` prime to `π`.
* `primary_sq_mod_four`, `sign_class_invariant`, `sign_even_power`: the 2-adic facts behind the
  signs.
* `lemma_2_2`: the splitting identity for truncated sums (Lemma 2.2).
* `corollary_2_3_reduce`, `corollary_2_3_general`: Corollary 2.3 for every valuation `e`: the
  reduction of `e` modulo `4` on the series prime to `π`, and the splitting with its terms at
  `k = 4j ≤ e` and `k = e + 1`.
* `two_term_split`, `corollary_2_3_odd`, `corollary_2_3_odd_inverse`, `corollary_2_3_coupled`:
  the four exact valuations `e = 0, 1, 2, 3` of Corollary 2.3, to which the reduction brings every
  series prime to `π`.
* `determinant_lower`, `determinant_ne_zero`, `determinant_r1`, `determinant_r3`,
  `determinant_coupled`: the determinants are bounded below on `σ ≥ 1`.
-/

open Complex Finset Filter Asymptotics Topology
open scoped ContDiff

noncomputable section

namespace FixedNumerator


/-- `λ³ = (1 + i)³ = -2 + 2i`. -/
def lam3 : GaussianInt := ⟨-2, 2⟩

/-- `c` is primary: `c ≡ 1 (mod λ³)`. -/
def IsPrimary (c : GaussianInt) : Prop := lam3 ∣ c - 1

/-- DDHL (3.3): `C(a, c) = ((N a - 1)/4)((N c - 1)/4)`. -/
def C (a c : GaussianInt) : ℤ := ((a.norm - 1) / 4) * ((c.norm - 1) / 4)

/-- The Gaussian integers of norm at most `X`. -/
def normBall (X : ℕ) : Finset GaussianInt :=
  ((Icc (-(X : ℤ)) X ×ˢ Icc (-(X : ℤ)) X).image fun ab => (⟨ab.1, ab.2⟩ : GaussianInt)).filter
    fun c => c.norm ≤ X

/-- A quartic residue symbol `χ r c = (r/c)₄` and a quartic Gauss sum `g μ c = g₄(μ, c)` on the
Gaussian integers, with the identities of DDHL §3 used in the local computation. -/
structure QuarticData where
  /-- The quartic residue symbol `(r/c)₄`. -/
  χ : GaussianInt → GaussianInt → ℂ
  /-- The quartic Gauss sum `g₄(μ, c)`. -/
  g : GaussianInt → GaussianInt → ℂ
  /-- The symbol is multiplicative in the numerator. -/
  chi_mul_left : ∀ a b c, χ (a * b) c = χ a c * χ b c
  /-- The symbol is multiplicative in the (primary) denominator. -/
  chi_mul_right : ∀ a c d, IsPrimary c → IsPrimary d → χ a (c * d) = χ a c * χ a d
  /-- On coprime pairs the symbol is a fourth root of unity. -/
  chi_pow_four : ∀ a c, IsCoprime a c → χ a c ^ 4 = 1
  /-- Biquadratic reciprocity, DDHL (3.2). -/
  reciprocity : ∀ a c, IsPrimary a → IsPrimary c → IsCoprime a c →
    χ a c = (-1 : ℂ) ^ C a c * χ c a
  /-- The twist rule, DDHL (3.4). -/
  g_twist : ∀ r μ c, IsPrimary c → IsCoprime r c → g (r * μ) c = starRingEnd ℂ (χ r c) * g μ c
  /-- Twisted multiplicativity, DDHL (3.5). -/
  g_mul : ∀ μ c c', IsPrimary c → IsPrimary c' → IsCoprime c c' →
    g μ (c * c') = χ c c' * χ c' c * g μ c * g μ c'
  /-- `g₄(μ, 1) = 1`, the case `ℓ = 0` of DDHL (3.7). -/
  g_one : ∀ μ, g μ 1 = 1
  /-- The support part of the local formula DDHL (3.7), with (3.4): for a primary prime `π` and
  `μ'` prime to `π`, `g₄(π^e μ', π^k)` vanishes unless `k = 0`, `k = e + 1`, or `4 ∣ k ≤ e`. -/
  g_prime_pow : ∀ π μ' (e k : ℕ), Prime π → IsPrimary π → IsCoprime μ' π →
    g (π ^ e * μ') (π ^ k) ≠ 0 → k = 0 ∨ k = e + 1 ∨ (4 ∣ k ∧ k ≤ e)

open Classical in
/-- `∑_{N(c) ≤ X, c ≡ β (mod 4), (c, γ) = 1} g₄(μ, c) W(c)`: the truncation at norm `X` of DDHL's
series `ψ*_β(s, μ, ℓ; γ)`, with the weight `W(c)` standing for `(c/|c|)^ℓ N(c)^{-s}`. -/
def truncSum (D : QuarticData) (W : GaussianInt → ℂ) (μ β γ : GaussianInt) (X : ℕ) : ℂ :=
  ∑ c ∈ (normBall X).filter (fun c => (4 : GaussianInt) ∣ c - β ∧ IsCoprime c γ), D.g μ c * W c


/-- **DDHL (3.6)**: `g₄(μ, c c') = (-1)^{C(c', c)} g₄(μ c'², c) g₄(μ, c')` for coprime primary
`c, c'`, derived from (3.2), (3.4) and (3.5). -/
theorem ddhl_3_6 (D : QuarticData) (μ c c' : GaussianInt) (hc : IsPrimary c)
    (hc' : IsPrimary c') (hcc : IsCoprime c c') :
    D.g μ (c * c') = (-1 : ℂ) ^ C c' c * D.g (μ * c' ^ 2) c * D.g μ c' := by
  sorry

/-- **The splitting identity.** For a primary `π` and a primary `c'` prime to `π`,
`g₄(μ, π^k c') = (-1)^{C(c', π^k)} g₄(μ, π^k) g₄(μ π^{2k}, c')`, with no condition linking `μ`
and `π`. -/
theorem splitting_identity (D : QuarticData) (μ π c' : GaussianInt) (hπ : IsPrimary π)
    (hc' : IsPrimary c') (hcop : IsCoprime π c') (k : ℕ) :
    D.g μ (π ^ k * c') =
      (-1 : ℂ) ^ C c' (π ^ k) * D.g μ (π ^ k) * D.g (μ * π ^ (2 * k)) c' := by
  sorry

/-- **Periodicity in the numerator**: `g₄(μ π^{4j}, c) = g₄(μ, c)` for primary `c` prime to `π`. -/
theorem numerator_period (D : QuarticData) (μ π c : GaussianInt) (hc : IsPrimary c)
    (hcop : IsCoprime π c) (j : ℕ) : D.g (μ * π ^ (4 * j)) c = D.g μ c := by
  sorry

/-- A primary `π` satisfies `π² ≡ 1 (mod 4)`. -/
theorem primary_sq_mod_four (π : GaussianInt) (hπ : IsPrimary π) :
    (4 : GaussianInt) ∣ π ^ 2 - 1 := by
  sorry

/-- The sign `(-1)^{C(a, c)}` depends only on the class of `a` modulo `4` (for `a` in a primary
class). -/
theorem sign_class_invariant (a b c : GaussianInt) (hb : IsPrimary b)
    (h : (4 : GaussianInt) ∣ a - b) : (-1 : ℂ) ^ C a c = (-1 : ℂ) ^ C b c := by
  sorry

/-- For primary `π` and even `k`, `(-1)^{C(a, π^k)} = 1`. -/
theorem sign_even_power (π a : GaussianInt) (hπ : IsPrimary π) (k : ℕ) (hk : Even k) :
    (-1 : ℂ) ^ C a (π ^ k) = 1 := by
  sorry

/-- **Lemma 2.2, the splitting identity for truncated sums.** For a primary prime `π` prime to
`γ`, a primary `β`, and a completely multiplicative weight `W` (standing for
`(c/|c|)^ℓ N(c)^{-s}`),
`∑_{N(c) ≤ X, c ≡ β, (c, γ) = 1} g₄(μ, c) W(c)` equals
`∑_{k ≤ X} (-1)^{C(π^k β, π^k)} g₄(μ, π^k) W(π)^k ∑_{N(c') ≤ X / N(π)^k, c' ≡ π^k β, (c', πγ) = 1}
g₄(μ π^{2k}, c') W(c')`. -/
theorem lemma_2_2 (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (X : ℕ) :
    truncSum D W μ β γ X =
      ∑ k ∈ range (X + 1), (-1 : ℂ) ^ C (π ^ k * β) (π ^ k) * D.g μ (π ^ k) * W π ^ k *
        truncSum D W (μ * π ^ (2 * k)) (π ^ k * β) (π * γ) (X / π.norm.toNat ^ k) := by
  sorry

/-- **The splitting identity with two terms**, when `g₄(μ, π^k)` vanishes except at `k = 0, m`. -/
theorem two_term_split (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (m : ℕ) (hm : m ≠ 0)
    (hsupp : ∀ k, k ≠ 0 → k ≠ m → D.g μ (π ^ k) = 0) (X : ℕ) :
    truncSum D W μ β γ X = truncSum D W μ β (π * γ) X +
      (-1 : ℂ) ^ C (π ^ m * β) (π ^ m) * D.g μ (π ^ m) * W π ^ m *
        truncSum D W (μ * π ^ (2 * m)) (π ^ m * β) (π * γ) (X / π.norm.toNat ^ m) := by
  sorry

/-- **Corollary 2.3, cases `r = 1` and `r = 3`.** For `μ = π^e μ'` with `e ∈ {1, 3}` and `μ'`
prime to `π`: `S_γ(X) = S_{πγ}(X) + g₄(μ, π^{e+1}) W(π)^{e+1} S_{πγ}(X / N(π)^{e+1})`, the
truncated form of `ψ*(s, μ; γ) = Δ(s) ψ*(s, μ; πγ)`. -/
theorem corollary_2_3_odd (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ' β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e : ℕ) (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X = truncSum D W (π ^ e * μ') β (π * γ) X +
      D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1) *
        truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (e + 1)) := by
  sorry

/-- **The inverse of Corollary 2.3, cases `r = 1, 3`**, the truncated form of
`ψ*(s, μ; πγ) = Δ(s)⁻¹ ψ*(s, μ; γ)`. -/
theorem corollary_2_3_odd_inverse (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ' β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e : ℕ) (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X =
      ∑ j ∈ range (X + 1), (-(D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1))) ^ j *
        truncSum D W (π ^ e * μ') β γ (X / (π.norm.toNat ^ (e + 1)) ^ j) := by
  sorry

/-- **Corollary 2.3, cases `r = 0` and `r = 2`: the coupled pair** for the numerators `μ'` and
`π² μ'`, `μ'` prime to `π` (DDHL (8.6) and (8.7)). -/
theorem corollary_2_3_coupled (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ' β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (X : ℕ) :
    truncSum D W μ' β γ X = truncSum D W μ' β (π * γ) X +
        (-1 : ℂ) ^ C (π * β) π * D.g μ' π * W π *
          truncSum D W (π ^ 2 * μ') (π * β) (π * γ) (X / π.norm.toNat) ∧
      truncSum D W (π ^ 2 * μ') (π * β) γ X = truncSum D W (π ^ 2 * μ') (π * β) (π * γ) X +
        (-1 : ℂ) ^ C β (π ^ 3) * D.g (π ^ 2 * μ') (π ^ 3) * W π ^ 3 *
          truncSum D W μ' β (π * γ) (X / π.norm.toNat ^ 3) := by
  sorry

/-- **Corollary 2.3, first claim: reduction of the valuation.** On the series prime to `π`, the
numerator `π^e μ'` may be replaced by `π^{e mod 4} μ'`, for every `e`. -/
theorem corollary_2_3_reduce (D : QuarticData) (W : GaussianInt → ℂ) (π γ μ' β : GaussianInt)
    (hβ : IsPrimary β) (e X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X = truncSum D W (π ^ (e % 4) * μ') β (π * γ) X := by
  sorry

/-- **Corollary 2.3 for every valuation.** For `μ = π^e μ'` with `μ'` prime to `π` and any
`e ≥ 0`, the terms of Lemma 2.2 that survive are `k = 4j ≤ e` and `k = e + 1`:
`S_γ(μ, β)(X) = ∑_{4j ≤ e} g₄(μ, π^{4j}) W(π)^{4j} S_{πγ}(μ, β)(X / N(π)^{4j})
  + (-1)^{C(π^{e+1}β, π^{e+1})} g₄(μ, π^{e+1}) W(π)^{e+1} S_{πγ}(μ π^{2(e+1)}, π^{e+1}β)(X / N(π)^{e+1})`.
For `e ≤ 3` the sum has the single term `j = 0`; for `e = 5`, for example, the terms are
`k = 0, 4, 6`. -/
theorem corollary_2_3_general (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ' β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X =
      ∑ j ∈ range (e / 4 + 1), D.g (π ^ e * μ') (π ^ (4 * j)) * W π ^ (4 * j) *
          truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (4 * j)) +
        (-1 : ℂ) ^ C (π ^ (e + 1) * β) (π ^ (e + 1)) * D.g (π ^ e * μ') (π ^ (e + 1)) *
          W π ^ (e + 1) *
          truncSum D W (π ^ e * μ' * π ^ (2 * (e + 1))) (π ^ (e + 1) * β) (π * γ)
            (X / π.norm.toNat ^ (e + 1)) := by
  sorry

/-- If `‖a‖ ≤ N^A` and `‖w‖ = N^{-σ}`, then `1 - N^{A - kσ} ≤ ‖1 + a w^k‖`. -/
theorem determinant_lower (N A σ : ℝ) (hN : 0 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) : 1 - N ^ (A - k * σ) ≤ ‖1 + a * w ^ k‖ := by
  sorry

/-- `1 + a w^k ≠ 0` when `‖a‖ ≤ N^A`, `‖w‖ = N^{-σ}`, `N > 1` and `A < kσ`. -/
theorem determinant_ne_zero (N A σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) (h : A < k * σ) : 1 + a * w ^ k ≠ 0 := by
  sorry

/-- **The determinant of case `r = 1`**: `‖a‖ ≤ N^{3/2}` and `σ ≥ 1` give
`‖1 + a w²‖ ≥ 1 - N^{-1/2} > 0`. -/
theorem determinant_r1 (N σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ ((3 : ℝ) / 2))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-(1 : ℝ) / 2) ∧ 1 - N ^ (-(1 : ℝ) / 2) ≤ ‖1 + a * w ^ 2‖ := by
  sorry

/-- **The determinant of case `r = 3`** (DDHL's `Δ(s, ℓ; π)`): `‖a‖ ≤ N³` and `σ ≥ 1` give
`‖1 + a w⁴‖ ≥ 1 - N^{-1} > 0`. -/
theorem determinant_r3 (N σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ (3 : ℝ))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 + a * w ^ 4‖ := by
  sorry

/-- **The determinant of the coupled pair**: `‖a₁‖ ≤ N^{1/2}`, `‖a₃‖ ≤ N^{5/2}` and `σ ≥ 1` give
`‖1 - a₁ a₃ w⁴‖ ≥ 1 - N^{-1} > 0`. -/
theorem determinant_coupled (N σ : ℝ) (hN : 1 < N) (a₁ a₃ w : ℂ)
    (ha₁ : ‖a₁‖ ≤ N ^ ((1 : ℝ) / 2)) (ha₃ : ‖a₃‖ ≤ N ^ ((5 : ℝ) / 2)) (hw : ‖w‖ = N ^ (-σ))
    (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 - a₁ * a₃ * w ^ 4‖ := by
  sorry

end FixedNumerator
