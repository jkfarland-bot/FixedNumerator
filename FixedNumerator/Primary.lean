module

public import FixedNumerator.Defs

@[expose] public section

/-!
# Primary Gaussian integers

* `lam3_dvd_four`: `λ³ ∣ 4`, so a class modulo `4` of a primary element is primary.
* `sq_sub_one`: a primary `π` satisfies `π² ≡ 1 (mod 4)`.
* `norm_mod_four`: a primary element has norm `≡ 1 (mod 4)`.
* `C_congr`: the parity of `(N a - 1)/4` depends only on the class of a primary `a` modulo `4`.
* `C_even_pow`: `C(a, π^k)` is even for even `k`.
-/

open Complex Finset

namespace FixedNumerator

lemma lam3_dvd_four : lam3 ∣ (4 : GaussianInt) := ⟨⟨-1, -1⟩, by decide⟩

lemma IsPrimary.mul {a b : GaussianInt} (ha : IsPrimary a) (hb : IsPrimary b) :
    IsPrimary (a * b) := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  refine ⟨s * (b - 1) + s + t, ?_⟩
  have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
  rw [this, hs, ht]; ring

lemma IsPrimary.pow {a : GaussianInt} (ha : IsPrimary a) (k : ℕ) : IsPrimary (a ^ k) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih => rw [pow_succ]; exact ih.mul ha

lemma isPrimary_one : IsPrimary 1 := ⟨0, by simp⟩

lemma IsPrimary.of_dvd_sub {a b : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ a - b) :
    IsPrimary a := by
  have h' : lam3 ∣ a - b := dvd_trans lam3_dvd_four h
  have : a - 1 = (a - b) + (b - 1) := by ring
  rw [IsPrimary, this]; exact dvd_add h' hb

/-- A primary `π` satisfies `π² ≡ 1 (mod 4)`. -/
lemma sq_sub_one {π : GaussianInt} (hπ : IsPrimary π) : (4 : GaussianInt) ∣ π ^ 2 - 1 := by
  obtain ⟨t, ht⟩ := hπ
  have hπ' : π = 1 + lam3 * t := by rw [← ht]; ring
  refine ⟨⟨-1, 1⟩ * t + ⟨0, -2⟩ * t ^ 2, ?_⟩
  rw [hπ']
  simp only [lam3]
  ext <;> simp [pow_two] <;> ring

/-- `π^(2k) ≡ 1 (mod 4)` for primary `π`. -/
lemma pow_two_mul_sub_one {π : GaussianInt} (hπ : IsPrimary π) (k : ℕ) :
    (4 : GaussianInt) ∣ π ^ (2 * k) - 1 := by
  rw [pow_mul]
  exact dvd_trans (sq_sub_one hπ) (sub_one_dvd_pow_sub_one _ k)

lemma norm_mod_four {a : GaussianInt} (ha : IsPrimary a) : a.norm % 4 = 1 := by
  obtain ⟨t, ht⟩ := ha
  have ha' : a = 1 + lam3 * t := by rw [← ht]; ring
  have hn : a.norm = 1 + 4 * (-(t.re) - t.im) + 8 * (t.re ^ 2 + t.im ^ 2) := by
    rw [ha']; simp [Zsqrtd.norm, lam3]; ring
  rw [hn]; omega

lemma norm_sub_mod_eight {a b : GaussianInt} (h : (4 : GaussianInt) ∣ a - b) :
    (8 : ℤ) ∣ a.norm - b.norm := by
  obtain ⟨t, ht⟩ := h
  have ha : a = b + 4 * t := by rw [← ht]; ring
  refine ⟨b.re * t.re + b.im * t.im + 2 * (t.re ^ 2 + t.im ^ 2), ?_⟩
  rw [ha]; simp [Zsqrtd.norm]; ring

/-- The parity of `(N a - 1)/4` depends only on the class of a primary `a` modulo `4`. -/
lemma quarter_parity {a b : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ a - b) :
    (a.norm - 1) / 4 % 2 = (b.norm - 1) / 4 % 2 := by
  have h8 := norm_sub_mod_eight h
  have h4 := norm_mod_four hb
  omega

lemma neg_one_zpow_congr {m n : ℤ} (h : m % 2 = n % 2) : (-1 : ℂ) ^ m = (-1 : ℂ) ^ n := by
  rcases Int.emod_two_eq_zero_or_one m with hm | hm
  · rw [Even.neg_one_zpow (Int.even_iff.mpr hm), Even.neg_one_zpow (Int.even_iff.mpr (h ▸ hm))]
  · rw [Odd.neg_one_zpow (Int.odd_iff.mpr hm), Odd.neg_one_zpow (Int.odd_iff.mpr (h ▸ hm))]

/-- The sign `(-1)^{C(a, c)}` depends only on the class of a primary `a` modulo `4`. -/
lemma C_sign_congr {a b c : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ a - b) :
    (-1 : ℂ) ^ C a c = (-1 : ℂ) ^ C b c := by
  apply neg_one_zpow_congr
  unfold C
  rw [Int.mul_emod, quarter_parity hb h, ← Int.mul_emod]

lemma C_symm (a c : GaussianInt) : C a c = C c a := by unfold C; ring

/-- For even `k`, `(N π^k - 1)/4` is even, so `(-1)^{C(a, π^k)} = 1`. -/
lemma C_sign_even_pow {π : GaussianInt} (hπ : IsPrimary π) (a : GaussianInt) {k : ℕ}
    (hk : Even k) : (-1 : ℂ) ^ C a (π ^ k) = 1 := by
  obtain ⟨j, rfl⟩ := hk
  have h4 : (4 : GaussianInt) ∣ π ^ (j + j) - 1 := by
    rw [← two_mul]; exact pow_two_mul_sub_one hπ j
  have h8 := norm_sub_mod_eight h4
  have hq : (π ^ (j + j)).norm - 1 = 8 * (((π ^ (j + j)).norm - 1) / 8) := by
    simp at h8; omega
  apply Even.neg_one_zpow
  unfold C
  apply Even.mul_left
  rw [Int.even_iff]; omega

lemma C_one_left (c : GaussianInt) : C 1 c = 0 := by simp [C, Zsqrtd.norm]

lemma C_one_right (c : GaussianInt) : C c 1 = 0 := by simp [C, Zsqrtd.norm]

end FixedNumerator
