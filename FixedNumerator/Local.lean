module

public import FixedNumerator.Primary

@[expose] public section

/-!
# The local identities

From the identities of DDHL §3 packaged in `QuarticData`:

* `g_mul_sq`: DDHL (3.6), `g₄(μ, c c') = (-1)^{C(c', c)} g₄(μ c'², c) g₄(μ, c')`;
* `g_split`: for a primary `π` and a primary `c'` prime to `π`,
  `g₄(μ, π^k c') = (-1)^{C(c', π^k)} g₄(μ, π^k) g₄(μ π^{2k}, c')`, with no condition linking
  `μ` and `π`;
* `g_mul_pow_four`: `g₄(μ π^{4j}, c) = g₄(μ, c)` for `c` prime to `π`;
* `g_eq_conj_chi_mul`: `g₄(ν, c) = conj((ν/c)₄) g₄(1, c)` for `c` prime to `ν`.
-/

open Complex Finset

namespace FixedNumerator

namespace QuarticData

variable (D : QuarticData)

lemma conj_sq_of_pow_four {x : ℂ} (hx : x ^ 4 = 1) : starRingEnd ℂ (x ^ 2) = x ^ 2 := by
  have hn : ‖x‖ = 1 := by
    have h := congrArg norm hx
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) (by norm_num)).mp h
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hn
  have hc : starRingEnd ℂ x = x⁻¹ := (Complex.inv_eq_conj hn).symm
  rw [map_pow, hc, inv_pow]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hx)

lemma neg_one_zpow_sq (m : ℤ) : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num

lemma chi_one_left (c : GaussianInt) : D.χ 1 c = 1 := by
  have h4 := D.chi_pow_four 1 c isCoprime_one_left
  have hm : D.χ 1 c = D.χ 1 c * D.χ 1 c := by
    have := D.chi_mul_left 1 1 c; rwa [mul_one] at this
  have h0 : D.χ 1 c ≠ 0 := by rintro h; rw [h] at h4; norm_num at h4
  exact mul_left_cancel₀ h0 (show D.χ 1 c * D.χ 1 c = D.χ 1 c * 1 by rw [mul_one]; exact hm.symm)

lemma chi_one_right (a : GaussianInt) : D.χ a 1 = 1 := by
  have h4 := D.chi_pow_four a 1 isCoprime_one_right
  have hm : D.χ a 1 = D.χ a 1 * D.χ a 1 := by
    have := D.chi_mul_right a 1 1 isPrimary_one isPrimary_one; rwa [mul_one] at this
  have h0 : D.χ a 1 ≠ 0 := by rintro h; rw [h] at h4; norm_num at h4
  exact mul_left_cancel₀ h0 (show D.χ a 1 * D.χ a 1 = D.χ a 1 * 1 by rw [mul_one]; exact hm.symm)

lemma chi_pow_left (a c : GaussianInt) (n : ℕ) : D.χ (a ^ n) c = D.χ a c ^ n := by
  induction n with
  | zero => simpa using D.chi_one_left c
  | succ n ih => rw [pow_succ, D.chi_mul_left, ih, pow_succ]

lemma chi_pow_right (a : GaussianInt) {π : GaussianInt} (hπ : IsPrimary π) (n : ℕ) :
    D.χ a (π ^ n) = D.χ a π ^ n := by
  induction n with
  | zero => simpa using D.chi_one_right a
  | succ n ih => rw [pow_succ, D.chi_mul_right a _ _ (hπ.pow n) hπ, ih, pow_succ]

/-- DDHL (3.6): `g₄(μ, c c') = (-1)^{C(c', c)} g₄(μ c'², c) g₄(μ, c')` for coprime primary
`c, c'`. -/
theorem g_mul_sq (μ : GaussianInt) {c c' : GaussianInt} (hc : IsPrimary c) (hc' : IsPrimary c')
    (hcc : IsCoprime c c') :
    D.g μ (c * c') = (-1 : ℂ) ^ C c' c * D.g (μ * c' ^ 2) c * D.g μ c' := by
  have h4 : D.χ c' c ^ 4 = 1 := D.chi_pow_four c' c hcc.symm
  have htw : D.g (μ * c' ^ 2) c = starRingEnd ℂ (D.χ c' c ^ 2) * D.g μ c := by
    rw [mul_comm μ, D.g_twist _ _ _ hc (hcc.symm.pow_left), D.chi_pow_left]
  rw [D.g_mul μ c c' hc hc' hcc, htw, conj_sq_of_pow_four h4, D.reciprocity c c' hc hc' hcc,
    C_symm c c']
  ring

/-- **The splitting identity.** For a primary `π` and a primary `c'` prime to `π`,
`g₄(μ, π^k c') = (-1)^{C(c', π^k)} g₄(μ, π^k) g₄(μ π^{2k}, c')`. No condition links `μ` and `π`. -/
theorem g_split (μ : GaussianInt) {π c' : GaussianInt} (hπ : IsPrimary π) (hc' : IsPrimary c')
    (hcop : IsCoprime π c') (k : ℕ) :
    D.g μ (π ^ k * c') =
      (-1 : ℂ) ^ C c' (π ^ k) * D.g μ (π ^ k) * D.g (μ * π ^ (2 * k)) c' := by
  have hk : IsCoprime (π ^ k) c' := hcop.pow_left
  rw [D.g_mul_sq μ (hπ.pow k) hc' hk]
  have h4 : D.χ π c' ^ 4 = 1 := D.chi_pow_four π c' hcop
  have hrec : D.χ c' π ^ 2 = D.χ π c' ^ 2 := by
    rw [D.reciprocity c' π hc' hπ hcop.symm, mul_pow, neg_one_zpow_sq, one_mul]
  have h1 : D.g (μ * c' ^ 2) (π ^ k) = starRingEnd ℂ ((D.χ π c' ^ 2) ^ k) * D.g μ (π ^ k) := by
    rw [mul_comm μ, D.g_twist _ _ _ (hπ.pow k) hk.symm.pow_left, D.chi_pow_left,
      D.chi_pow_right _ hπ, ← pow_mul, mul_comm k 2, pow_mul, hrec]
  have h2 : D.g (μ * π ^ (2 * k)) c' = starRingEnd ℂ ((D.χ π c' ^ 2) ^ k) * D.g μ c' := by
    rw [mul_comm μ, D.g_twist _ _ _ hc' hcop.pow_left, D.chi_pow_left, pow_mul]
  rw [h1, h2]; ring

/-- `g₄(μ π^{4j}, c) = g₄(μ, c)` for primary `c` prime to `π`. -/
theorem g_mul_pow_four (μ : GaussianInt) {π c : GaussianInt} (hc : IsPrimary c)
    (hcop : IsCoprime π c) (j : ℕ) : D.g (μ * π ^ (4 * j)) c = D.g μ c := by
  rw [mul_comm μ, D.g_twist _ _ _ hc hcop.pow_left, D.chi_pow_left, pow_mul,
    D.chi_pow_four π c hcop, one_pow, map_one, one_mul]

/-- `g₄(ν, c) = conj((ν/c)₄) g₄(1, c)` for primary `c` prime to `ν` (Lemma 2.1(i)). -/
theorem g_eq_conj_chi_mul (ν : GaussianInt) {c : GaussianInt} (hc : IsPrimary c)
    (hcop : IsCoprime ν c) : D.g ν c = starRingEnd ℂ (D.χ ν c) * D.g 1 c := by
  simpa using D.g_twist ν 1 c hc hcop

end QuarticData

end FixedNumerator
