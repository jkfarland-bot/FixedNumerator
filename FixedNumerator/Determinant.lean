module

public import FixedNumerator.Cases

@[expose] public section

/-!
# The determinants

With `w = W(π)` of modulus `N(π)^{-σ}`:

* `det_lower`: if `‖a‖ ≤ N^A` then `1 - N^{A - kσ} ≤ ‖1 + a w^k‖`;
* `det_ne_zero`: so `1 + a w^k ≠ 0` when `A < kσ`;
* `delta_r1_lower`: `‖a‖ ≤ N^{3/2}`, `k = 2`, `σ ≥ 1` give `‖1 + a w²‖ ≥ 1 - N^{-1/2} > 0`
  (case `r = 1`, where `|g₄(πμ', π²)| = N(π)^{3/2}`);
* `delta_r3_lower`: `‖a‖ ≤ N³`, `k = 4`, `σ ≥ 1` give `‖1 + a w⁴‖ ≥ 1 - N^{-1} > 0`
  (case `r = 3`, where `g₄(π³μ', π⁴) = -N(π)³`, so this is DDHL's `Δ(s, ℓ; π)`);
* `delta_coupled_lower`: `‖a₁‖ ≤ N^{1/2}`, `‖a₃‖ ≤ N^{5/2}` give `‖1 - a₁ a₃ w⁴‖ ≥ 1 - N^{-1}`
  (the determinant of the coupled pair).
-/

open Complex Real

namespace FixedNumerator

lemma one_sub_norm_le_norm_one_add (t : ℂ) : 1 - ‖t‖ ≤ ‖1 + t‖ := by
  have := norm_sub_norm_le (1 : ℂ) (-t)
  simpa [sub_neg_eq_add] using this

/-- If `‖a‖ ≤ N^A` and `‖w‖ = N^{-σ}`, then `1 - N^{A - kσ} ≤ ‖1 + a w^k‖`. -/
theorem det_lower {N A σ : ℝ} (hN : 0 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ A) (hw : ‖w‖ = N ^ (-σ))
    (k : ℕ) : 1 - N ^ (A - k * σ) ≤ ‖1 + a * w ^ k‖ := by
  have hwk : ‖w ^ k‖ = N ^ (-(k * σ)) := by
    rw [norm_pow, hw, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]; ring_nf
  have hbound : ‖a * w ^ k‖ ≤ N ^ (A - k * σ) := by
    rw [norm_mul, hwk, sub_eq_add_neg, Real.rpow_add hN]
    exact mul_le_mul_of_nonneg_right ha (by positivity)
  linarith [one_sub_norm_le_norm_one_add (a * w ^ k)]

/-- `1 + a w^k ≠ 0` when `‖a‖ ≤ N^A`, `‖w‖ = N^{-σ}`, `N > 1` and `A < kσ`. -/
theorem det_ne_zero {N A σ : ℝ} (hN : 1 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) (h : A < k * σ) : 1 + a * w ^ k ≠ 0 := by
  intro h0
  have := det_lower (by linarith) ha hw k
  rw [h0, norm_zero] at this
  have : N ^ (A - k * σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN (by linarith)
  linarith

/-- **The determinant of case `r = 1`.** -/
theorem delta_r1_lower {N σ : ℝ} (hN : 1 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ ((3 : ℝ) / 2))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-(1 : ℝ) / 2) ∧ 1 - N ^ (-(1 : ℝ) / 2) ≤ ‖1 + a * w ^ 2‖ := by
  constructor
  · have := Real.rpow_lt_one_of_one_lt_of_neg hN (show -(1 : ℝ) / 2 < 0 by norm_num)
    linarith
  · have h := det_lower (by linarith) ha hw 2
    have : N ^ ((3 : ℝ) / 2 - (2 : ℕ) * σ) ≤ N ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (by push_cast; linarith)
    linarith

/-- **The determinant of case `r = 3`**, DDHL's `Δ(s, ℓ; π)`. -/
theorem delta_r3_lower {N σ : ℝ} (hN : 1 < N) {a w : ℂ} (ha : ‖a‖ ≤ N ^ (3 : ℝ))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 + a * w ^ 4‖ := by
  constructor
  · have := Real.rpow_lt_one_of_one_lt_of_neg hN (show (-1 : ℝ) < 0 by norm_num)
    linarith
  · have h := det_lower (by linarith) ha hw 4
    have : N ^ ((3 : ℝ) - (4 : ℕ) * σ) ≤ N ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (by push_cast; linarith)
    linarith

/-- **The determinant of the coupled pair** (cases `r = 0, 2`). -/
theorem delta_coupled_lower {N σ : ℝ} (hN : 1 < N) {a₁ a₃ w : ℂ}
    (ha₁ : ‖a₁‖ ≤ N ^ ((1 : ℝ) / 2)) (ha₃ : ‖a₃‖ ≤ N ^ ((5 : ℝ) / 2)) (hw : ‖w‖ = N ^ (-σ))
    (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 - a₁ * a₃ * w ^ 4‖ := by
  have hN0 : 0 < N := by linarith
  have ha : ‖-(a₁ * a₃)‖ ≤ N ^ (3 : ℝ) := by
    rw [norm_neg, norm_mul]
    calc ‖a₁‖ * ‖a₃‖ ≤ N ^ ((1 : ℝ) / 2) * N ^ ((5 : ℝ) / 2) :=
          mul_le_mul ha₁ ha₃ (norm_nonneg _) (by positivity)
      _ = N ^ (3 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num
  have := delta_r3_lower hN ha hw hσ
  simpa [sub_eq_add_neg, neg_mul] using this

end FixedNumerator
