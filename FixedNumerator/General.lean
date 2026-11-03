module

public import FixedNumerator.Cases

@[expose] public section

/-!
# Corollary 2.3 for every valuation

* `truncSum_reduce_num`: the first claim of Corollary 2.3. On the series prime to `π`, the
  numerator `π^e μ'` may be replaced by `π^r μ'` with `r = e mod 4`.
* `truncSum_general`: the splitting identity for `μ = π^e μ'` with any `e`. By the support of
  `g₄(μ, π^k)` (DDHL (3.7)) the surviving terms are `k = 4j ≤ e` and `k = e + 1`; at `k = 4j` the
  sign is `1`, the numerator `μ π^{8j}` reduces to `μ` and the class `π^{4j} β` to `β`. For
  `e ≥ 4` this has more than two terms: at `e = 5`, the terms `k = 0, 4, 6`.
-/

open Complex Finset

namespace FixedNumerator

namespace QuarticData

variable (D : QuarticData)

/-- **Corollary 2.3, first claim.** `S_{πγ}(π^e μ', β)(X) = S_{πγ}(π^{e mod 4} μ', β)(X)`. -/
theorem truncSum_reduce_num (W : GaussianInt → ℂ) {π γ : GaussianInt} (μ' β : GaussianInt)
    (hβ : IsPrimary β) (e X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X = truncSum D W (π ^ (e % 4) * μ') β (π * γ) X := by
  have h : π ^ e * μ' = π ^ (e % 4) * μ' * π ^ (4 * (e / 4)) := by
    rw [mul_right_comm, ← pow_add, Nat.mod_add_div]
  rw [h, D.truncSum_num_pow_four W _ hβ]

/-- **Corollary 2.3 for every valuation.** For `μ = π^e μ'`, `μ'` prime to `π`, and any `e`,
`S_γ(μ, β)(X) = ∑_{4j ≤ e} g₄(μ, π^{4j}) W(π)^{4j} S_{πγ}(μ, β)(X / N(π)^{4j})
  + (-1)^{C(π^{e+1}β, π^{e+1})} g₄(μ, π^{e+1}) W(π)^{e+1} S_{πγ}(μ π^{2(e+1)}, π^{e+1}β)(X / N(π)^{e+1})`.
The term `j = 0` is `S_{πγ}(μ, β)(X)`. -/
theorem truncSum_general (W : GaussianInt → ℂ) (hW1 : W 1 = 1)
    (hW : ∀ a b, W (a * b) = W a * W b) {π γ μ' : GaussianInt} (β : GaussianInt) (hπ : Prime π)
    (hπp : IsPrimary π) (hπγ : IsCoprime π γ) (hβ : IsPrimary β) (hμ' : IsCoprime μ' π)
    (e X : ℕ) :
    truncSum D W (π ^ e * μ') β γ X =
      ∑ j ∈ range (e / 4 + 1), D.g (π ^ e * μ') (π ^ (4 * j)) * W π ^ (4 * j) *
          truncSum D W (π ^ e * μ') β (π * γ) (X / π.norm.toNat ^ (4 * j)) +
        (-1 : ℂ) ^ C (π ^ (e + 1) * β) (π ^ (e + 1)) * D.g (π ^ e * μ') (π ^ (e + 1)) *
          W π ^ (e + 1) *
          truncSum D W (π ^ e * μ' * π ^ (2 * (e + 1))) (π ^ (e + 1) * β) (π * γ)
            (X / π.norm.toNat ^ (e + 1)) := by
  classical
  set μ := π ^ e * μ' with hμdef
  set F : ℕ → ℂ := fun k => (-1 : ℂ) ^ C (π ^ k * β) (π ^ k) * D.g μ (π ^ k) * W π ^ k *
    truncSum D W (μ * π ^ (2 * k)) (π ^ k * β) (π * γ) (X / π.norm.toNat ^ k) with hF
  have hN2 := two_le_norm_of_prime hπ
  -- terms beyond `X` vanish
  have hbig : ∀ k, X < k → F k = 0 := by
    intro k hk
    have hdiv : X / π.norm.toNat ^ k = 0 := by
      apply Nat.div_eq_of_lt
      calc X < 2 ^ k := lt_trans hk Nat.lt_two_pow_self
        _ ≤ π.norm.toNat ^ k := Nat.pow_le_pow_left (by omega) k
    simp only [hF, hdiv, D.truncSum_zero W _ _ ((hπp.pow k).mul hβ), mul_zero]
  -- terms off the support vanish
  have hsupp : ∀ k, k ≠ e + 1 → ¬ (4 ∣ k ∧ k ≤ e) → F k = 0 := by
    intro k hk1 hk2
    have : D.g μ (π ^ k) = 0 := by
      by_contra hne
      rcases D.g_prime_pow π μ' e k hπ hπp hμ' hne with h | h | h
      · exact hk2 ⟨h ▸ dvd_zero 4, by omega⟩
      · exact hk1 h
      · exact hk2 h
    simp only [hF, this, mul_zero, zero_mul]
  -- the support as a finset
  set K : Finset ℕ := insert (e + 1) ((range (e / 4 + 1)).image (fun j => 4 * j)) with hK
  have hnot : e + 1 ∉ (range (e / 4 + 1)).image (fun j => 4 * j) := by
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro j hj; omega
  have hsplit := D.truncSum_split W hW1 hW μ β hπ hπp hπγ hβ X
  -- both sums equal the sum over `range M`
  set M := max (X + 1) (e + 2) with hM
  have h1 : ∑ k ∈ range (X + 1), F k = ∑ k ∈ range M, F k := by
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk; simp only [Finset.mem_range, not_lt] at hk; exact hbig k (by omega)
  have h2 : ∑ k ∈ K, F k = ∑ k ∈ range M, F k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [hK, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hk ⊢
      rcases hk with rfl | ⟨j, hj, rfl⟩ <;> omega
    · intro k _ hk
      simp only [hK, Finset.mem_insert, Finset.mem_image, Finset.mem_range, not_or,
        not_exists, not_and] at hk
      apply hsupp k hk.1
      rintro ⟨⟨j, rfl⟩, hle⟩
      exact hk.2 j (by omega) rfl
  rw [hsplit]
  change ∑ k ∈ range (X + 1), F k = _
  rw [h1, ← h2, hK, Finset.sum_insert hnot, Finset.sum_image (by intro a _ b _ h; simp only at h; omega),
    add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hev : Even (4 * j) := ⟨2 * j, by ring⟩
  have hcl : (4 : GaussianInt) ∣ π ^ (4 * j) * β - β := by
    have : π ^ (4 * j) * β - β = (π ^ (2 * (2 * j)) - 1) * β := by ring_nf
    rw [this]; exact dvd_mul_of_dvd_left (pow_two_mul_sub_one hπp (2 * j)) _
  simp only [hF]
  rw [C_sign_even_pow hπp _ hev, one_mul, D.truncSum_congr_class W _ _ hcl,
    show 2 * (4 * j) = 4 * (2 * j) by ring, D.truncSum_num_pow_four W _ hβ]

end QuarticData

end FixedNumerator
