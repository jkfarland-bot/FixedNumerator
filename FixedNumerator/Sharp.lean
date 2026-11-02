module

public import FixedNumerator.Determinant

@[expose] public section

/-!
# Removing the smoothing (Corollary 1.2)

`sharp_of_smooth`: let `a : ℕ → ℂ` be such that `∑_{n ≤ x} ‖a n‖ ~ κ x` (for the sums of
Corollary 1.2 this is the prime ideal theorem, since `|g̃₄(ν, c)| ≤ 1` away from finitely many `c`),
and suppose that for every smooth `R` supported in some `[δ, 1]` with `δ > 0` the smoothed sums
`∑ a n R(n/X)` are `o(X)` (Theorem 1.1, which gives `O(X^{5/6+ε})`). Then the sharp sums
`∑_{n ≤ X} a n` are `o(X)`.
-/

open Complex Finset Filter Asymptotics Topology
open scoped ContDiff

namespace FixedNumerator

lemma countAbs_nonneg (a : ℕ → ℂ) (x : ℝ) : 0 ≤ countAbs a x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma countAbs_natCast (a : ℕ → ℂ) (X : ℕ) : countAbs a X = ∑ n ∈ Icc 1 X, ‖a n‖ := by
  simp [countAbs]

/-- `countAbs a (t X) / X → κ t` for `t > 0`. -/
lemma tendsto_countAbs_scaled {a : ℕ → ℂ} {κ : ℝ}
    (hmean : Tendsto (fun x : ℝ => countAbs a x / x) atTop (𝓝 κ)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun X : ℕ => countAbs a (t * X) / X) atTop (𝓝 (κ * t)) := by
  have h1 : Tendsto (fun X : ℕ => t * (X : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop ht tendsto_natCast_atTop_atTop
  have h2 := (hmean.comp h1).mul_const t
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  simp only [Function.comp]
  field_simp

/-- **Corollary 1.2: removing the smoothing.** -/
theorem sharp_of_smooth (a : ℕ → ℂ) (κ : ℝ)
    (hmean : Tendsto (fun x : ℝ => countAbs a x / x) atTop (𝓝 κ))
    (hsmooth : ∀ R : ℝ → ℝ, ContDiff ℝ ∞ R → (∃ δ > 0, Function.support R ⊆ Set.Icc δ 1) →
      (fun X : ℕ => smoothSum a R X) =o[atTop] (fun X : ℕ => (X : ℝ))) :
    (fun X : ℕ => sharpSum a X) =o[atTop] (fun X : ℕ => (X : ℝ)) := by
  classical
  have hκ : 0 ≤ κ := by
    refine ge_of_tendsto hmean ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_nonneg (countAbs_nonneg a x) hx.le
  rw [isLittleO_iff]
  intro c hc
  set η : ℝ := min (1 / 4) (c / (8 * (κ + 1))) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hκη : κ * η ≤ c / 8 := by
    have h1 : η ≤ c / (8 * (κ + 1)) := min_le_right _ _
    have h2 : κ * η ≤ κ * (c / (8 * (κ + 1))) := mul_le_mul_of_nonneg_left h1 hκ
    have h3 : κ * (c / (8 * (κ + 1))) ≤ c / 8 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  -- the smooth weight: `1` on `[η, 1 - η]`, supported in `(η/2, 1 - η/2)`
  let f : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2 - η, 1 / 2 - η / 2, by linarith, by linarith⟩
  have hsupp : Function.support (f : ℝ → ℝ) ⊆ Set.Icc (η / 2) 1 := by
    rw [f.support_eq, Real.ball_eq_Ioo]
    intro x hx
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]
    show η / 2 ≤ x ∧ x ≤ 1
    have : (f.rOut : ℝ) = 1 / 2 - η / 2 := rfl
    constructor <;> linarith [hx.1, hx.2]
  have hone : ∀ x : ℝ, η ≤ x → x ≤ 1 - η → f x = 1 := by
    intro x h1 h2
    apply f.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    have : (f.rIn : ℝ) = 1 / 2 - η := rfl
    constructor <;> linarith
  have hR := hsmooth f f.contDiff ⟨η / 2, by linarith, hsupp⟩
  rw [isLittleO_iff] at hR
  have hRe := hR (show (0 : ℝ) < c / 4 by positivity)
  -- the two edges
  have hE1 := tendsto_countAbs_scaled hmean hη0
  have hE2 := tendsto_countAbs_scaled hmean (show (0 : ℝ) < 1 by norm_num)
  have hE3 := tendsto_countAbs_scaled hmean (show (0 : ℝ) < 1 - η by linarith)
  have hE23 := hE2.sub hE3
  have hlim23 : κ * 1 - κ * (1 - η) = κ * η := by ring
  rw [hlim23] at hE23
  have ev1 := (hE1.eventually (gt_mem_nhds (show κ * η < κ * η + c / 16 by linarith)))
  have ev2 := (hE23.eventually (gt_mem_nhds (show κ * η < κ * η + c / 16 by linarith)))
  filter_upwards [hRe, ev1, ev2, eventually_gt_atTop 0] with X hRX h1 h2 hX
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  rw [div_lt_iff₀ hX'] at h1
  rw [← sub_div, div_lt_iff₀ hX'] at h2
  -- pointwise: `1 - R(n/X) ≤ [n < ηX] + [(1-η)X < n]`
  have hpt : ∀ n ∈ Icc 1 X, ‖a n‖ * (1 - f (n / X)) ≤
      (if (n : ℝ) < η * X then ‖a n‖ else 0) + (if (1 - η) * X < n then ‖a n‖ else 0) := by
    intro n _
    have hf0 := f.nonneg (x := (n : ℝ) / X)
    have hf1 := f.le_one (x := (n : ℝ) / X)
    have han := norm_nonneg (a n)
    by_cases hlo : (n : ℝ) < η * X
    · have : (1 - η) * X < n ∨ ¬ (1 - η) * X < n := em _
      rcases this with h | h <;> simp [hlo, h] <;> nlinarith
    · by_cases hhi : (1 - η) * X < n
      · simp [hlo, hhi]; nlinarith
      · push Not at hlo hhi
        have : f (n / X) = 1 := hone _ (by rw [le_div_iff₀ hX']; linarith)
          (by rw [div_le_iff₀ hX']; linarith)
        rw [this, sub_self, mul_zero]
        split_ifs <;> linarith
  have hsum : ‖sharpSum a X - smoothSum a f X‖ ≤
      countAbs a (η * X) + (countAbs a (1 * X) - countAbs a ((1 - η) * X)) := by
    have hdiff : sharpSum a X - smoothSum a f X =
        ∑ n ∈ Icc 1 X, a n * ((1 - f (n / X) : ℝ) : ℂ) := by
      simp only [sharpSum, smoothSum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro n _; push_cast; ring
    rw [hdiff]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Icc 1 X, ‖a n * ((1 - f (n / X) : ℝ) : ℂ)‖ = ‖a n‖ * (1 - f (n / X)) := by
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [f.le_one (x := (n : ℝ) / X)])]
    rw [Finset.sum_congr rfl hterm]
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
    apply add_le_add
    · -- lower edge
      unfold countAbs
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn
        simp only [Finset.mem_Icc]
        exact ⟨hn.1.1, Nat.le_floor hn.2.le⟩
      · intros; exact norm_nonneg _
    · -- upper edge
      have hsplit := Finset.sum_filter_add_sum_filter_not (Icc 1 X)
        (fun n : ℕ => (1 - η) * X < n) (fun n => ‖a n‖)
      have hlow : (Icc 1 X).filter (fun n : ℕ => ¬ (1 - η) * X < n) = Icc 1 ⌊(1 - η) * X⌋₊ := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc, not_lt]
        have hnn : (0 : ℝ) ≤ (1 - η) * X := by nlinarith
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, Nat.le_floor h3⟩
        · rintro ⟨h1, h3⟩
          have h4 : (n : ℝ) ≤ (1 - η) * X := le_trans (by exact_mod_cast h3) (Nat.floor_le hnn)
          refine ⟨⟨h1, ?_⟩, h4⟩
          have : (n : ℝ) ≤ X := by nlinarith
          exact_mod_cast this
      rw [hlow] at hsplit
      have hX1 : countAbs a (1 * X) = ∑ n ∈ Icc 1 X, ‖a n‖ := by
        rw [one_mul, countAbs_natCast]
      rw [hX1, ← hsplit]
      unfold countAbs
      linarith
  have hfin : ‖sharpSum a X‖ ≤ ‖smoothSum a f X‖ + ‖sharpSum a X - smoothSum a f X‖ := by
    have := norm_add_le (smoothSum a f X) (sharpSum a X - smoothSum a f X)
    simpa using this
  have hRX' : ‖smoothSum a f X‖ ≤ c / 4 * X := by
    simpa [Real.norm_of_nonneg hX'.le] using hRX
  rw [Real.norm_of_nonneg hX'.le]
  have hκηX : κ * η * X ≤ c / 8 * X := mul_le_mul_of_nonneg_right hκη hX'.le
  have hcX : 0 ≤ c * X := by positivity
  nlinarith [hsum, hfin, hRX', h1, h2]
