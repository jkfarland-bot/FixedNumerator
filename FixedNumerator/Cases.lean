module

public import FixedNumerator.Split

@[expose] public section

/-!
# Removing a prime of the numerator (Corollary 2.3)

* `truncSum_two_term`: if `g₄(μ, π^k)` vanishes except at `k = 0` and `k = m`, the splitting
  identity has two terms.
* `truncSum_single`: for `μ = π^e μ'` with `e ∈ {1, 3}` and `μ'` prime to `π`, the two terms
  close up: `S_γ(μ, β)(X) = S_{πγ}(μ, β)(X) + a S_{πγ}(μ, β)(X / N(π)^{e+1})` with
  `a = g₄(μ, π^{e+1}) W(π)^{e+1}`. This is the truncated form of
  `ψ*(s, μ; γ) = Δ(s) ψ*(s, μ; πγ)`.
* `truncSum_single_inv`: the inverse, `S_{πγ}(μ, β)(X) = ∑_j (-a)^j S_γ(μ, β)(X / N(π)^{(e+1)j})`,
  the truncated form of `1/Δ(s)`.
* `truncSum_coupled`: for `μ'` prime to `π`, the coupled pair for the numerators `μ'` and
  `π² μ'` (the cases `e ≡ 0, 2`), which is DDHL (8.6) and (8.7).
-/

open Complex Finset

namespace FixedNumerator

namespace QuarticData

variable (D : QuarticData)

lemma truncSum_zero (W : GaussianInt → ℂ) (μ γ : GaussianInt) {β : GaussianInt}
    (hβ : IsPrimary β) : truncSum D W μ β γ 0 = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro c hc
  simp only [Finset.mem_filter, mem_normBall] at hc
  exfalso
  have h0 : c = 0 := by
    have := norm_nonneg' c
    exact (Zsqrtd.norm_eq_zero_iff (by norm_num) c).mp (by push_cast at hc; omega)
  subst h0
  exact not_four_dvd_zero_sub hβ hc.2.1

lemma truncSum_congr_class (W : GaussianInt → ℂ) (μ γ : GaussianInt) {β β' : GaussianInt}
    (h : (4 : GaussianInt) ∣ β - β') (X : ℕ) :
    truncSum D W μ β γ X = truncSum D W μ β' γ X := by
  classical
  unfold truncSum
  congr 1
  apply Finset.filter_congr
  intro c _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have : c - β' = (c - β) + (β - β') := by ring
    rw [this]; exact dvd_add h1 h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have : c - β = (c - β') - (β - β') := by ring
    rw [this]; exact dvd_sub h1 h

lemma truncSum_num_pow_four (W : GaussianInt → ℂ) (μ : GaussianInt) {π γ β : GaussianInt}
    (hβ : IsPrimary β) (j X : ℕ) :
    truncSum D W (μ * π ^ (4 * j)) β (π * γ) X = truncSum D W μ β (π * γ) X := by
  classical
  unfold truncSum
  apply Finset.sum_congr rfl
  intro c hc
  simp only [Finset.mem_filter] at hc
  have hcp : IsPrimary c := hβ.of_dvd_sub hc.2.1
  have hcop : IsCoprime π c := (IsCoprime.mul_right_iff.mp hc.2.2).1.symm
  rw [D.g_mul_pow_four μ hcp hcop j]

/-- The splitting identity with two surviving terms. -/
theorem truncSum_two_term (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ : GaussianInt} (μ β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) {m : ℕ} (hm : m ≠ 0)
    (hsupp : ∀ k, k ≠ 0 → k ≠ m → D.g μ (π ^ k) = 0) (X : ℕ) :
    truncSum D W μ β γ X = truncSum D W μ β (π * γ) X +
      (-1 : ℂ) ^ C (π ^ m * β) (π ^ m) * D.g μ (π ^ m) * W π ^ m *
        truncSum D W (μ * π ^ (2 * m)) (π ^ m * β) (π * γ) (X / π.norm.toNat ^ m) := by
  rw [D.truncSum_split W hW1 hW μ β hπ hπp hπγ hβ X]
  rw [Finset.sum_eq_add 0 m (Ne.symm hm)]
  · simp [C_one_right, D.g_one]
  · intro k _ hk
    rw [hsupp k hk.1 hk.2]; simp
  · intro h; simp at h
  · intro h
    simp only [Finset.mem_range, not_lt] at h
    have hN2 := two_le_norm_of_prime hπ
    have hdiv : X / π.norm.toNat ^ m = 0 := by
      apply Nat.div_eq_of_lt
      have h1 : X < 2 ^ m := lt_trans (show X < m by omega) Nat.lt_two_pow_self
      calc X < 2 ^ m := h1
        _ ≤ π.norm.toNat ^ m := Nat.pow_le_pow_left (by omega) m
    rw [hdiv, D.truncSum_zero W _ _ ((hπp.pow m).mul hβ)]
    simp

/-- **Corollary 2.3, cases `r = 1` and `r = 3`.** For `μ = π^e μ'` with `e ∈ {1, 3}` and `μ'` prime
to `π`, with `a = g₄(μ, π^{e+1}) W(π)^{e+1}`:
`S_γ(μ, β)(X) = S_{πγ}(μ, β)(X) + a S_{πγ}(μ, β)(X / N(π)^{e+1})`. -/
theorem truncSum_single (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    {e : ℕ} (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X = truncSum D W (π ^ e * μ') β (π * γ) X +
      D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1) *
        truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (e + 1)) := by
  have hsupp : ∀ k, k ≠ 0 → k ≠ e + 1 → D.g (π ^ e * μ') (π ^ k) = 0 := by
    intro k hk0 hke
    by_contra hne
    rcases D.g_prime_pow π μ' e k hπ hπp hμ' hne with h | h | ⟨h4, hle⟩
    · exact hk0 h
    · exact hke h
    · rcases he with rfl | rfl <;> omega
  have hev : Even (e + 1) := by rcases he with rfl | rfl <;> decide
  rw [D.truncSum_two_term W hW1 hW _ β hπ hπp hπγ hβ (by omega) hsupp X,
    C_sign_even_pow hπp _ hev, one_mul]
  have h2 : 2 * (e + 1) = 4 * ((e + 1) / 2) := by rcases he with rfl | rfl <;> rfl
  rw [h2, D.truncSum_num_pow_four W _ ((hπp.pow _).mul hβ),
    D.truncSum_congr_class W _ _ (show (4 : GaussianInt) ∣ π ^ (e + 1) * β - β from ?_)]
  obtain ⟨j, hj⟩ := hev
  have : π ^ (e + 1) * β - β = (π ^ (2 * j) - 1) * β := by rw [hj, two_mul]; ring
  rw [this]; exact dvd_mul_of_dvd_left (pow_two_mul_sub_one hπp j) _

/-- Inverting `S(Y) = T(Y) + a T(Y / M)`: `T(X) = ∑_{j ≤ X} (-a)^j S(X / M^j)`. -/
lemma invert_two_term (S T : ℕ → ℂ) (a : ℂ) {M : ℕ} (hM : 2 ≤ M) (hT0 : T 0 = 0)
    (h : ∀ Y, S Y = T Y + a * T (Y / M)) :
    ∀ X n, X + 1 ≤ n → T X = ∑ j ∈ range n, (-a) ^ j * S (X / M ^ j) := by
  have hS0 : S 0 = 0 := by rw [h 0, Nat.zero_div, hT0]; ring
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.div_one, one_mul]
    rcases Nat.eq_zero_or_pos X with hX | hX
    · subst hX
      rw [hT0, hS0]
      simp [hS0]
    · have hlt : X / M < X := Nat.div_lt_self hX (by omega)
      have hle : X / M + 1 ≤ n' := by
        have : X / M ≤ X / 2 := Nat.div_le_div_left hM (by norm_num)
        omega
      have hT : T X = S X - a * T (X / M) := by rw [h X]; ring
      rw [hT, ih (X / M) hlt n' hle, Finset.mul_sum]
      rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      ring

/-- **The inverse of Corollary 2.3, cases `r = 1, 3`**, the truncated form of
`ψ*(s, μ; πγ) = Δ(s)⁻¹ ψ*(s, μ; γ)`. -/
theorem truncSum_single_inv (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    {e : ℕ} (he : e = 1 ∨ e = 3) (X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X =
      ∑ j ∈ range (X + 1), (-(D.g (π ^ e * μ') (π ^ (e + 1)) * W π ^ (e + 1))) ^ j *
        truncSum D W (π ^ e * μ') β γ (X / (π.norm.toNat ^ (e + 1)) ^ j) := by
  have hN2 := two_le_norm_of_prime hπ
  apply invert_two_term (fun Y => truncSum D W (π ^ e * μ') β γ Y)
    (fun Y => truncSum D W (π ^ e * μ') β (π * γ) Y)
  · calc 2 ≤ π.norm.toNat := by omega
      _ ≤ π.norm.toNat ^ (e + 1) := Nat.le_self_pow (by omega) _
  · exact D.truncSum_zero W _ _ hβ
  · intro Y; exact D.truncSum_single W hW1 hW β hπ hπp hπγ hβ hμ' he Y
  · exact le_refl _

/-- **Corollary 2.3, cases `r = 0` and `r = 2`: the coupled pair.** For `μ'` prime to `π`, the
numerators `μ'` and `π² μ'` are linked by
`S_γ(μ', β) = S_{πγ}(μ', β) + (-1)^{C(πβ, π)} g₄(μ', π) W(π) S_{πγ}(π² μ', πβ)(X / N(π))` and
`S_γ(π² μ', πβ) = S_{πγ}(π² μ', πβ) + (-1)^{C(β, π³)} g₄(π² μ', π³) W(π)³ S_{πγ}(μ', β)(X / N(π)³)`.
These are DDHL (8.6) and (8.7); eliminating gives (8.8). -/
theorem truncSum_coupled (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (X : ℕ) :
    truncSum D W μ' β γ X = truncSum D W μ' β (π * γ) X +
        (-1 : ℂ) ^ C (π * β) π * D.g μ' π * W π *
          truncSum D W (π ^ 2 * μ') (π * β) (π * γ) (X / π.norm.toNat) ∧
      truncSum D W (π ^ 2 * μ') (π * β) γ X = truncSum D W (π ^ 2 * μ') (π * β) (π * γ) X +
        (-1 : ℂ) ^ C β (π ^ 3) * D.g (π ^ 2 * μ') (π ^ 3) * W π ^ 3 *
          truncSum D W μ' β (π * γ) (X / π.norm.toNat ^ 3) := by
  have hsupp0 : ∀ k, k ≠ 0 → k ≠ 1 → D.g μ' (π ^ k) = 0 := by
    intro k hk0 hk1
    by_contra hne
    have := D.g_prime_pow π μ' 0 k hπ hπp hμ' (by simpa using hne)
    omega
  have hsupp2 : ∀ k, k ≠ 0 → k ≠ 3 → D.g (π ^ 2 * μ') (π ^ k) = 0 := by
    intro k hk0 hk3
    by_contra hne
    have := D.g_prime_pow π μ' 2 k hπ hπp hμ' hne
    omega
  have hπβ : IsPrimary (π * β) := hπp.mul hβ
  constructor
  · rw [D.truncSum_two_term W hW1 hW μ' β hπ hπp hπγ hβ one_ne_zero hsupp0 X]
    simp only [pow_one]
    congr 2
    rw [show μ' * π ^ (2 * 1) = π ^ 2 * μ' by ring]
  · rw [D.truncSum_two_term W hW1 hW (π ^ 2 * μ') (π * β) hπ hπp hπγ hπβ (by norm_num) hsupp2 X]
    have hcl : (4 : GaussianInt) ∣ π ^ 3 * (π * β) - β := by
      have : π ^ 3 * (π * β) - β = (π ^ (2 * 2) - 1) * β := by ring
      rw [this]; exact dvd_mul_of_dvd_left (pow_two_mul_sub_one hπp 2) _
    rw [C_sign_congr hβ hcl, D.truncSum_congr_class W _ _ hcl,
      show π ^ 2 * μ' * π ^ (2 * 3) = μ' * π ^ (4 * 2) by ring,
      D.truncSum_num_pow_four W μ' hβ]

end QuarticData

end FixedNumerator
