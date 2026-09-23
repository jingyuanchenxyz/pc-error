import LatentError.Lemmas.Noise
import LatentError.Lemmas.Convergence

/-!
# Proposition 3: the observable dual `W⁽ᵖ⁾` in the limit

(a) `ZᵀZ/(np) → (δ²/n) Iₙ` from Kolmogorov's strong law (Fact 1);
(b) `bᵀZ/√p → 0` from Lemma 4;
(c) `W⁽ᵖ⁾ → W = W₀ + (δ²/n) Iₙ`; (d) eigenpairs via Weyl (Fact 2) and Lemma 2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory Matrix MatrixOrder

noncomputable section

namespace PCError

/-! ## Kolmogorov's strong law, re-indexed -/

/-- `(1/p) Σ_{i=1}^p yᵢ → 0` implies `(1/p) Σ_{i<p} yᵢ → 0`. -/
lemma tendsto_avg_range_of_Icc {y : ℕ → ℝ}
    (h : Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.Icc 1 p, y i) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.range p, y i) atTop (𝓝 0) := by
  set A : ℕ → ℝ := fun p => (1 / (p : ℝ)) * ∑ i ∈ Finset.Icc 1 p, y i
  -- `y (p+1) / (p+1) = A (p+1) - (p/(p+1)) A p`
  have hIcc : ∀ p, ∑ i ∈ Finset.Icc 1 (p + 1), y i = ∑ i ∈ Finset.Icc 1 p, y i + y (p + 1) :=
    fun p => Finset.sum_Icc_succ_top (by omega) _
  have hyp : Tendsto (fun p : ℕ => y (p + 1) / ((p : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun p : ℕ => A (p + 1)) atTop (𝓝 0) := h.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun p : ℕ => ((p : ℝ) / ((p : ℝ) + 1)) * A p) atTop (𝓝 (1 * 0)) :=
      (tendsto_natCast_div_add_atTop (1 : ℝ)).mul h
    have h3 := h1.sub h2
    rw [mul_zero, sub_zero] at h3
    refine h3.congr' (Filter.Eventually.of_forall fun p => ?_)
    simp only [A, hIcc, Nat.cast_add, Nat.cast_one]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · have : (0 : ℝ) < p := Nat.cast_pos.2 hp
      field_simp
      ring
  have hrange : ∀ p, ∑ i ∈ Finset.range p, y i =
      ∑ i ∈ Finset.Icc 1 p, y i + y 0 - y p := by
    intro p
    induction p with
    | zero => simp
    | succ p ih => rw [Finset.sum_range_succ, ih, hIcc]; ring
  have hy0 : Tendsto (fun p : ℕ => y 0 * (1 / (p : ℝ))) atTop (𝓝 (y 0 * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
  have hypp : Tendsto (fun p : ℕ => y p / (p : ℝ)) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simpa [Nat.cast_add, Nat.cast_one] using hyp
  have := (h.add hy0).sub hypp
  rw [mul_zero, add_zero, sub_zero] at this
  refine this.congr' (Filter.Eventually.of_forall fun p => ?_)
  dsimp only
  rw [hrange]
  simp only [A]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have : (0 : ℝ) < p := Nat.cast_pos.2 hp
    field_simp

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Fact 1 for `range p` sums. -/
lemma slln_range (hFact1 : Fact1_SLLN) {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hL2 : ∀ i, MemLp (X i) 2 μ) (hind : iIndepFun X μ) {C : ℝ}
    (hvar : ∀ i, variance (X i) μ ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.range p, (X i ω - μ[X i]))
      atTop (𝓝 0) := by
  have hC : 0 ≤ C := (variance_nonneg _ _).trans (hvar 0)
  have hsum : Summable (fun i : ℕ => variance (X i) μ / (i : ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => div_nonneg (variance_nonneg _ _) (sq_nonneg _))
      (fun i => ?_) ((Real.summable_one_div_nat_pow.2 one_lt_two).mul_left C)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (hvar i) (sq_nonneg _)
  filter_upwards [hFact1 μ X hmeas hL2 hind hsum] with ω hω
  exact tendsto_avg_range_of_Icc hω

section noise

variable {n : ℕ} {var : ℕ → Fin n → ℝ} {κ4 : ℝ} (N : NoiseModel n var κ4 Ω μ)

/-- Diagonal entries: `(1/p) Σ_{i<p} Z²ᵢₗ → δ²`. -/
lemma NoiseModel.avg_sq (hFact1 : Fact1_SLLN) {δ2 : ℝ} (l : Fin n)
    (hA3 : Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.range p, var i l) atTop (𝓝 δ2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.range p, N.Z i l ω ^ 2)
      atTop (𝓝 δ2) := by
  have hind : iIndepFun (fun i ω => N.Z i l ω ^ 2) μ :=
    (N.indep_col l).comp (fun _ x => x ^ 2) fun _ => measurable_id.pow_const 2
  filter_upwards [slln_range hFact1 (fun i => (N.meas i l).pow_const 2) (fun i => N.memLp_sq i l)
    hind (fun i => N.variance_sq_le i l)] with ω hω
  have := hω.add hA3
  rw [zero_add] at this
  refine this.congr' (Filter.Eventually.of_forall fun p => ?_)
  simp only [N.integral_sq, Finset.sum_sub_distrib]
  ring

omit [IsProbabilityMeasure μ] in
lemma memLp_two_mul_of_memLp4 {f g : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ)
    (hfm : Measurable f) (hgm : Measurable g) : MemLp (fun ω => f ω * g ω) 2 μ := by
  have hf4 : Integrable (fun ω => f ω ^ 4) μ := by
    simpa [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] using
      hf.integrable_norm_pow (p := 4) (by norm_num)
  have hg4 : Integrable (fun ω => g ω ^ 4) μ := by
    simpa [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] using
      hg.integrable_norm_pow (p := 4) (by norm_num)
  refine (memLp_two_iff_integrable_sq (hfm.mul hgm).aestronglyMeasurable).2 ?_
  refine ((hf4.add hg4).div_const 2).mono' ((hfm.mul hgm).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
  exact sq_mul_sq_le _ _

/-- Off-diagonal entries: `(1/p) Σ_{i<p} Zᵢₗ Zᵢₘ → 0` for `l ≠ m`. -/
lemma NoiseModel.avg_cross (hFact1 : Fact1_SLLN) {l m : Fin n} (hlm : l ≠ m) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.range p, N.Z i l ω * N.Z i m ω)
      atTop (𝓝 0) := by
  have hind : iIndepFun (fun i ω => N.Z i l ω * N.Z i m ω) μ :=
    N.indep_rows.comp (fun _ v => v l * v m) fun _ =>
      (measurable_pi_apply l).mul (measurable_pi_apply m)
  have hmean : ∀ i, μ[fun ω => N.Z i l ω * N.Z i m ω] = 0 := by
    intro i
    have hlm' : ((i, l) : ℕ × Fin n) ≠ (i, m) := by simp [hlm]
    have hi := N.indep.indepFun hlm'
    rw [show (fun ω => N.Z i l ω * N.Z i m ω) = (N.Z i l * N.Z i m) from rfl,
      hi.integral_mul_eq_mul_integral (N.meas i l).aestronglyMeasurable
        (N.meas i m).aestronglyMeasurable, N.mean_zero, zero_mul]
  have hvar : ∀ i, variance (fun ω => N.Z i l ω * N.Z i m ω) μ ≤ κ4 := by
    intro i
    refine (variance_le_expectation_sq ((N.meas i l).mul (N.meas i m)).aestronglyMeasurable).trans ?_
    have h4 : Integrable (fun ω => N.Z i l ω ^ 4 + N.Z i m ω ^ 4) μ :=
      (N.integrable_pow4 i l).add (N.integrable_pow4 i m)
    have hint1 : Integrable (fun ω => (N.Z i l ω * N.Z i m ω) ^ 2) μ :=
      (memLp_two_iff_integrable_sq ((N.meas i l).mul (N.meas i m)).aestronglyMeasurable).1
        (memLp_two_mul_of_memLp4 (N.memLp4 i l) (N.memLp4 i m) (N.meas i l) (N.meas i m))
    have hle : ∀ ω, (N.Z i l ω * N.Z i m ω) ^ 2 ≤ (N.Z i l ω ^ 4 + N.Z i m ω ^ 4) / 2 :=
      fun ω => by rw [mul_pow]; exact sq_mul_sq_le _ _
    have hmono := integral_mono hint1 (h4.div_const 2) hle
    rw [integral_div, integral_add (N.integrable_pow4 i l) (N.integrable_pow4 i m)] at hmono
    refine le_trans (le_of_eq ?_) (hmono.trans ?_)
    · rfl
    · linarith [N.fourth_le i l, N.fourth_le i m]
  filter_upwards [slln_range hFact1 (fun i => (N.meas i l).mul (N.meas i m))
    (fun i => memLp_two_mul_of_memLp4 (N.memLp4 i l) (N.memLp4 i m) (N.meas i l) (N.meas i m))
    hind hvar] with ω hω
  refine hω.congr' (Filter.Eventually.of_forall fun p => ?_)
  simp only [hmean, sub_zero]

end noise

end PCError

end
