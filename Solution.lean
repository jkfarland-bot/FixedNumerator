module

public import FixedNumerator

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `FixedNumerator/`. The definitions used in the statements come from
`FixedNumerator/Defs.lean` and are compared with the copies in `Challenge.lean`.
-/

open Complex Finset Filter Asymptotics Topology
open scoped ContDiff

noncomputable section

namespace FixedNumerator


/-- **DDHL (3.6)**: `g₄(μ, c c') = (-1)^{C(c', c)} g₄(μ c'², c) g₄(μ, c')` for coprime primary
`c, c'`, derived from (3.2), (3.4) and (3.5). -/
theorem ddhl_3_6 (D : QuarticData) (μ c c' : GaussianInt) (hc : IsPrimary c)
    (hc' : IsPrimary c') (hcc : IsCoprime c c') :
    D.g μ (c * c') = (-1 : ℂ) ^ C c' c * D.g (μ * c' ^ 2) c * D.g μ c' :=
  D.g_mul_sq μ hc hc' hcc

/-- **The splitting identity.** For a primary `π` and a primary `c'` prime to `π`,
`g₄(μ, π^k c') = (-1)^{C(c', π^k)} g₄(μ, π^k) g₄(μ π^{2k}, c')`, with no condition linking `μ`
and `π`. -/
theorem splitting_identity (D : QuarticData) (μ π c' : GaussianInt) (hπ : IsPrimary π)
    (hc' : IsPrimary c') (hcop : IsCoprime π c') (k : ℕ) :
    D.g μ (π ^ k * c') =
      (-1 : ℂ) ^ C c' (π ^ k) * D.g μ (π ^ k) * D.g (μ * π ^ (2 * k)) c' :=
  D.g_split μ hπ hc' hcop k

/-- **Periodicity in the numerator**: `g₄(μ π^{4j}, c) = g₄(μ, c)` for primary `c` prime to `π`. -/
theorem numerator_period (D : QuarticData) (μ π c : GaussianInt) (hc : IsPrimary c)
    (hcop : IsCoprime π c) (j : ℕ) : D.g (μ * π ^ (4 * j)) c = D.g μ c :=
  D.g_mul_pow_four μ hc hcop j

/-- A primary `π` satisfies `π² ≡ 1 (mod 4)`. -/
theorem primary_sq_mod_four (π : GaussianInt) (hπ : IsPrimary π) :
    (4 : GaussianInt) ∣ π ^ 2 - 1 :=
  sq_sub_one hπ

/-- The sign `(-1)^{C(a, c)}` depends only on the class of `a` modulo `4` (for `a` in a primary
class). -/
theorem sign_class_invariant (a b c : GaussianInt) (hb : IsPrimary b)
    (h : (4 : GaussianInt) ∣ a - b) : (-1 : ℂ) ^ C a c = (-1 : ℂ) ^ C b c :=
  C_sign_congr hb h

/-- For primary `π` and even `k`, `(-1)^{C(a, π^k)} = 1`. -/
theorem sign_even_power (π a : GaussianInt) (hπ : IsPrimary π) (k : ℕ) (hk : Even k) :
    (-1 : ℂ) ^ C a (π ^ k) = 1 :=
  C_sign_even_pow hπ a hk

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
        truncSum D W (μ * π ^ (2 * k)) (π ^ k * β) (π * γ) (X / π.norm.toNat ^ k) :=
  D.truncSum_split W hW1 hW μ β hπ hπp hπγ hβ X

/-- **The splitting identity with two terms**, when `g₄(μ, π^k)` vanishes except at `k = 0, m`. -/
theorem two_term_split (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (m : ℕ) (hm : m ≠ 0)
    (hsupp : ∀ k, k ≠ 0 → k ≠ m → D.g μ (π ^ k) = 0) (X : ℕ) :
    truncSum D W μ β γ X = truncSum D W μ β (π * γ) X +
      (-1 : ℂ) ^ C (π ^ m * β) (π ^ m) * D.g μ (π ^ m) * W π ^ m *
        truncSum D W (μ * π ^ (2 * m)) (π ^ m * β) (π * γ) (X / π.norm.toNat ^ m) :=
  D.truncSum_two_term W hW1 hW μ β hπ hπp hπγ hβ hm hsupp X

/-- **Corollary 2.3, cases `r = 1` and `r = 3`.** For `μ = π^e μ'` with `e ∈ {1, 3}` and `μ'`
prime to `π`: `S_γ(X) = S_{πγ}(X) + g₄(μ, π^{e+1}) W(π)^{e+1} S_{πγ}(X / N(π)^{e+1})`, the
truncated form of `ψ*(s, μ; γ) = Δ(s) ψ*(s, μ; πγ)`. -/
theorem corollary_2_3_odd (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ' β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e : ℕ) (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X = truncSum D W (π ^ e * μ') β (π * γ) X +
      D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1) *
        truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (e + 1)) :=
  D.truncSum_single W hW1 hW β hπ hπp hπγ hβ hμ' he X

/-- **The inverse of Corollary 2.3, cases `r = 1, 3`**, the truncated form of
`ψ*(s, μ; πγ) = Δ(s)⁻¹ ψ*(s, μ; γ)`. -/
theorem corollary_2_3_odd_inverse (D : QuarticData) (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) (π γ μ' β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e : ℕ) (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X =
      ∑ j ∈ range (X + 1), (-(D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1))) ^ j *
        truncSum D W (π ^ e * μ') β γ (X / (π.norm.toNat ^ (e + 1)) ^ j) :=
  D.truncSum_single_inv W hW1 hW β hπ hπp hπγ hβ hμ' he X

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
          truncSum D W μ' β (π * γ) (X / π.norm.toNat ^ 3) :=
  D.truncSum_coupled W hW1 hW β hπ hπp hπγ hβ hμ' X

/-- If `‖a‖ ≤ N^A` and `‖w‖ = N^{-σ}`, then `1 - N^{A - kσ} ≤ ‖1 + a w^k‖`. -/
theorem determinant_lower (N A σ : ℝ) (hN : 0 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) : 1 - N ^ (A - k * σ) ≤ ‖1 + a * w ^ k‖ :=
  det_lower hN ha hw k

/-- `1 + a w^k ≠ 0` when `‖a‖ ≤ N^A`, `‖w‖ = N^{-σ}`, `N > 1` and `A < kσ`. -/
theorem determinant_ne_zero (N A σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) (h : A < k * σ) : 1 + a * w ^ k ≠ 0 :=
  det_ne_zero hN ha hw k h

/-- **The determinant of case `r = 1`**: `‖a‖ ≤ N^{3/2}` and `σ ≥ 1` give
`‖1 + a w²‖ ≥ 1 - N^{-1/2} > 0`. -/
theorem determinant_r1 (N σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ ((3 : ℝ) / 2))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-(1 : ℝ) / 2) ∧ 1 - N ^ (-(1 : ℝ) / 2) ≤ ‖1 + a * w ^ 2‖ :=
  delta_r1_lower hN ha hw hσ

/-- **The determinant of case `r = 3`** (DDHL's `Δ(s, ℓ; π)`): `‖a‖ ≤ N³` and `σ ≥ 1` give
`‖1 + a w⁴‖ ≥ 1 - N^{-1} > 0`. -/
theorem determinant_r3 (N σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ (3 : ℝ))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 + a * w ^ 4‖ :=
  delta_r3_lower hN ha hw hσ

/-- **The determinant of the coupled pair**: `‖a₁‖ ≤ N^{1/2}`, `‖a₃‖ ≤ N^{5/2}` and `σ ≥ 1` give
`‖1 - a₁ a₃ w⁴‖ ≥ 1 - N^{-1} > 0`. -/
theorem determinant_coupled (N σ : ℝ) (hN : 1 < N) (a₁ a₃ w : ℂ)
    (ha₁ : ‖a₁‖ ≤ N ^ ((1 : ℝ) / 2)) (ha₃ : ‖a₃‖ ≤ N ^ ((5 : ℝ) / 2)) (hw : ‖w‖ = N ^ (-σ))
    (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 - a₁ * a₃ * w ^ 4‖ :=
  delta_coupled_lower hN ha₁ ha₃ hw hσ

/-- **Corollary 1.2: removing the smoothing.** If `∑_{n ≤ x} ‖a n‖ ~ κ x` and the smoothed sums
`∑ a n R(n/X)` are `o(X)` for every smooth `R` supported in some `[δ, 1]` with `δ > 0`, then
`∑_{n ≤ X} a n = o(X)`. -/
theorem smoothing_removal (a : ℕ → ℂ) (κ : ℝ)
    (hmean : Tendsto (fun x : ℝ => countAbs a x / x) atTop (𝓝 κ))
    (hsmooth : ∀ R : ℝ → ℝ, ContDiff ℝ ∞ R → (∃ δ > 0, Function.support R ⊆ Set.Icc δ 1) →
      (fun X : ℕ => smoothSum a R X) =o[atTop] (fun X : ℕ => (X : ℝ))) :
    (fun X : ℕ => sharpSum a X) =o[atTop] (fun X : ℕ => (X : ℝ)) :=
  sharp_of_smooth a κ hmean hsmooth

end FixedNumerator
