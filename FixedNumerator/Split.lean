module

public import FixedNumerator.Local

@[expose] public section

/-!
# The splitting identity for truncated sums (Lemma 2.2)

For a primary prime `π` prime to `γ`, a primary class `β` and a completely multiplicative weight
`W`, `truncSum_split` writes the truncated series with the condition `(c, γ) = 1` as a finite
combination of truncated series with the condition `(c', πγ) = 1`:

`∑_{N(c) ≤ X, c ≡ β, (c, γ) = 1} g₄(μ, c) W(c) = ∑_k (-1)^{C(π^k β, π^k)} g₄(μ, π^k) W(π)^k ·
  ∑_{N(c') ≤ X / N(π)^k, c' ≡ π^k β, (c', πγ) = 1} g₄(μ π^{2k}, c') W(c')`.

This is DDHL (8.6) with no condition linking `μ` and `π`.
-/

open Complex Finset

namespace FixedNumerator

lemma int_neg_le_mul_self (n : ℤ) : -n ≤ n * n ∧ n ≤ n * n := by
  rcases le_or_gt 0 n with h | h <;> constructor <;> nlinarith

lemma norm_eq_sq (c : GaussianInt) : c.norm = c.re * c.re + c.im * c.im := by
  simp [Zsqrtd.norm]

lemma mem_normBall {X : ℕ} {c : GaussianInt} : c ∈ normBall X ↔ c.norm ≤ X := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(c.re, c.im), ?_, rfl⟩, h⟩
    have hn := norm_eq_sq c
    have h1 := int_neg_le_mul_self c.re
    have h2 := int_neg_le_mul_self c.im
    have h3 := mul_self_nonneg c.re
    have h4 := mul_self_nonneg c.im
    simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma norm_nonneg' (c : GaussianInt) : 0 ≤ c.norm := Zsqrtd.norm_nonneg (by norm_num) c

lemma norm_pow' (a : GaussianInt) (k : ℕ) : (a ^ k).norm = a.norm ^ k := by
  induction k with
  | zero => simp [Zsqrtd.norm]
  | succ k ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]

lemma norm_lam3 : lam3.norm = 8 := by simp [lam3, Zsqrtd.norm]

lemma not_four_dvd_zero_sub {b : GaussianInt} (hb : IsPrimary b) :
    ¬ (4 : GaussianInt) ∣ 0 - b := by
  intro h
  have h1 : lam3 ∣ (0 - b) + (b - 1) := dvd_add (dvd_trans lam3_dvd_four h) hb
  have h2 : lam3 ∣ 1 := by
    have : (0 - b) + (b - 1) = -1 := by ring
    rw [this] at h1; exact (dvd_neg).mp h1
  have hu : IsUnit lam3 := isUnit_of_dvd_one h2
  have := (Zsqrtd.norm_eq_one_iff' (by norm_num) lam3).mpr hu
  rw [norm_lam3] at this; norm_num at this

lemma ne_zero_of_four_dvd {b c : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ c - b) :
    c ≠ 0 := by
  rintro rfl; exact not_four_dvd_zero_sub hb h

lemma two_le_norm_of_prime {π : GaussianInt} (hπ : Prime π) : 2 ≤ π.norm := by
  have h0 : π.norm ≠ 0 := by
    intro h
    exact hπ.ne_zero ((Zsqrtd.norm_eq_zero_iff (by norm_num) π).mp h)
  have h1 : π.norm ≠ 1 := fun h => hπ.not_isUnit ((Zsqrtd.norm_eq_one_iff' (by norm_num) π).mp h)
  have := norm_nonneg' π
  omega

lemma toNat_norm (c : GaussianInt) : (c.norm.toNat : ℤ) = c.norm :=
  Int.toNat_of_nonneg (norm_nonneg' c)

lemma le_div_iff_norm {X M : ℕ} (hM : 0 < M) (c : GaussianInt) :
    c.norm ≤ ((X / M : ℕ) : ℤ) ↔ (M : ℤ) * c.norm ≤ X := by
  rw [← toNat_norm c]
  norm_cast
  rw [Nat.le_div_iff_mul_le hM, mul_comm]

/-- Uniqueness of `c = π^k c'` with `π ∤ c'`. -/
lemma pow_mul_inj {π a b : GaussianInt} (hπ : Prime π) (ha : ¬ π ∣ a) (hb : ¬ π ∣ b) {k j : ℕ}
    (h : π ^ k * a = π ^ j * b) : k = j ∧ a = b := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  rcases lt_trichotomy k j with hkj | hkj | hkj
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkj
    have : a = π ^ (d + 1) * b := by
      apply mul_left_cancel₀ (pow_ne_zero k hπ0)
      rw [h]; ring
    exact ha ⟨π ^ d * b, by rw [this]; ring⟩
  · subst hkj; exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero k hπ0) h⟩
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkj
    have : b = π ^ (d + 1) * a := by
      apply mul_left_cancel₀ (pow_ne_zero j hπ0)
      rw [← h]; ring
    exact hb ⟨π ^ d * a, by rw [this]; ring⟩

lemma weight_pow {W : GaussianInt → ℂ} (hW1 : W 1 = 1) (hW : ∀ a b, W (a * b) = W a * W b)
    (a : GaussianInt) (k : ℕ) : W (a ^ k) = W a ^ k := by
  induction k with
  | zero => simpa using hW1
  | succ k ih => rw [pow_succ, hW, ih, pow_succ]

namespace QuarticData

variable (D : QuarticData)

/-- **Lemma 2.2, the splitting identity for truncated sums.** -/
theorem truncSum_split (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ : GaussianInt} (μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (X : ℕ) :
    truncSum D W μ β γ X =
      ∑ k ∈ range (X + 1), (-1 : ℂ) ^ C (π ^ k * β) (π ^ k) * D.g μ (π ^ k) * W π ^ k *
        truncSum D W (μ * π ^ (2 * k)) (π ^ k * β) (π * γ) (X / π.norm.toNat ^ k) := by
  classical
  have hN2 := two_le_norm_of_prime hπ
  have hNpos : ∀ k : ℕ, 0 < π.norm.toNat ^ k := fun k => pow_pos (by omega) k
  have hNcast : ∀ k : ℕ, ((π.norm.toNat ^ k : ℕ) : ℤ) = π.norm ^ k := by
    intro k; push_cast; rw [toNat_norm]
  simp only [truncSum, Finset.mul_sum]
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => π ^ x.1 * x.2) ?_ ?_ ?_ ?_
  · -- maps into the left side
    rintro ⟨k, c'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, mem_normBall] at hx
    obtain ⟨_, hn, hcl, hcop⟩ := hx
    simp only [Finset.mem_filter, mem_normBall]
    refine ⟨?_, ?_, ?_⟩
    · rw [Zsqrtd.norm_mul, norm_pow']
      rw [le_div_iff_norm (hNpos k), hNcast] at hn
      exact hn
    · have h2 := pow_two_mul_sub_one hπp k
      have : π ^ k * c' - β = π ^ k * (c' - π ^ k * β) + (π ^ (2 * k) - 1) * β := by ring
      rw [this]; exact dvd_add (dvd_mul_of_dvd_right hcl _) (dvd_mul_of_dvd_left h2 _)
    · exact IsCoprime.mul_left_iff.mpr ⟨hπγ.pow_left, (IsCoprime.mul_right_iff.mp hcop).2⟩
  · -- injective
    rintro ⟨k, a⟩ ha ⟨j, b⟩ hb h
    simp only [Finset.mem_sigma, Finset.mem_filter] at ha hb
    have hpa : ¬ π ∣ a := fun hd =>
      (hπ.coprime_iff_not_dvd.mp (IsCoprime.mul_right_iff.mp ha.2.2.2).1.symm) hd
    have hpb : ¬ π ∣ b := fun hd =>
      (hπ.coprime_iff_not_dvd.mp (IsCoprime.mul_right_iff.mp hb.2.2.2).1.symm) hd
    obtain ⟨h1, h2⟩ := pow_mul_inj hπ hpa hpb h
    subst h1; subst h2; rfl
  · -- surjective
    intro c hc
    simp only [Finset.mem_filter, mem_normBall] at hc
    obtain ⟨hn, hcl, hcop⟩ := hc
    have hc0 : c ≠ 0 := ne_zero_of_four_dvd hβ hcl
    have hfin := FiniteMultiplicity.of_not_isUnit hπ.not_isUnit hc0
    obtain ⟨c', hcc', hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    set k := multiplicity π c
    have hc'0 : c' ≠ 0 := by rintro rfl; simp at hcc'; exact hc0 hcc'
    have hnc' : 1 ≤ c'.norm := by
      have := norm_nonneg' c'
      have h0 : c'.norm ≠ 0 := fun h => hc'0 ((Zsqrtd.norm_eq_zero_iff (by norm_num) c').mp h)
      omega
    have hnorm : c.norm = π.norm ^ k * c'.norm := by rw [hcc', Zsqrtd.norm_mul, norm_pow']
    have hkX : k < X + 1 := by
      have h2k : (2 : ℤ) ^ k ≤ π.norm ^ k := pow_le_pow_left₀ (by norm_num) hN2 k
      have hpk : (0 : ℤ) ≤ π.norm ^ k := le_trans (by positivity) h2k
      have : (2 : ℤ) ^ k ≤ X := by nlinarith
      have hk2 : (k : ℤ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
      omega
    have hcop' : IsCoprime c' π := (hπ.coprime_iff_not_dvd.mpr hnd).symm
    have hcopγ : IsCoprime c' γ := by
      rw [hcc'] at hcop; exact (IsCoprime.mul_left_iff.mp hcop).2
    refine ⟨⟨k, c'⟩, ?_, hcc'.symm⟩
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, mem_normBall]
    refine ⟨hkX, ?_, ?_, IsCoprime.mul_right_iff.mpr ⟨hcop', hcopγ⟩⟩
    · rw [le_div_iff_norm (hNpos k), hNcast, ← hnorm]; exact hn
    · have h2 := pow_two_mul_sub_one hπp k
      have : c' - π ^ k * β = π ^ k * (π ^ k * c' - β) - (π ^ (2 * k) - 1) * c' := by ring
      rw [this, ← hcc']
      exact dvd_sub (dvd_mul_of_dvd_right hcl _) (dvd_mul_of_dvd_left h2 _)
  · -- the summands agree
    rintro ⟨k, c'⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter] at hx
    obtain ⟨_, _, hcl, hcop⟩ := hx
    have hkβ : IsPrimary (π ^ k * β) := (hπp.pow k).mul hβ
    have hc'p : IsPrimary c' := hkβ.of_dvd_sub hcl
    have hcop' : IsCoprime π c' := (IsCoprime.mul_right_iff.mp hcop).1.symm
    simp only
    rw [D.g_split μ hπp hc'p hcop' k, C_sign_congr hkβ hcl, hW, weight_pow hW1 hW]
    ring

end QuarticData

end FixedNumerator
