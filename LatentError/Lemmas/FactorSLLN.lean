import LatentError.Lemmas.Prop3
import LatentError.Lemmas.AlgLeaves

/-!
# The remark after Corollary 3: the strong law for one entry of `F Fᵀ/n`

For an i.i.d.-type factor sequence `f⁽ˡ⁾` (Assumption 1 plus independence across dates and a
uniform fourth-moment bound), `(1/n) Σ_{l<n} f⁽ˡ⁾_a f⁽ˡ⁾_b → Σ_f(a,b)` almost surely.

The proof is the one of `NoiseModel.avg_cross` (`Lemmas/Prop3.lean`) with `Z` replaced by the
factor coordinates: the products `X l = f⁽ˡ⁾_a f⁽ˡ⁾_b` are independent, square integrable,
have mean `Σ_f(a,b)` and variance at most `κ_f`, so Kolmogorov's strong law (Fact 1, via
`slln_range`) applies.  This file isolates those four facts as leaf lemmas.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

noncomputable section

namespace PCError

variable {k : ℕ} {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f : ℕ → Ω → Fin k → ℝ}

/-- One coordinate of one factor draw is measurable. -/
lemma factor_coord_meas (hmeas : ∀ l, Measurable (f l)) (l : ℕ) (a : Fin k) :
    Measurable (fun ω => f l ω a) := by
  -- sketch: exact (measurable_pi_apply a).comp (hmeas l)
  fun_prop

/-- The products `f⁽ˡ⁾_a f⁽ˡ⁾_b`, `l = 0, 1, …`, are independent. -/
lemma factor_prod_indep (hindep : iIndepFun f μ) (a b : Fin k) :
    iIndepFun (fun l ω => f l ω a * f l ω b) μ := by
  -- sketch: as in `NoiseModel.avg_cross`:
  -- exact hindep.comp (fun _ v => v a * v b)
  --   (fun _ => (measurable_pi_apply a).mul (measurable_pi_apply b))
  exact hindep.comp (fun _ v => v a * v b) fun _ => (measurable_pi_apply a).mul (measurable_pi_apply b)

/-- Each product is square integrable. -/
lemma factor_prod_memLp2 (hmeas : ∀ l, Measurable (f l))
    (hmom : ∀ l a, MemLp (fun ω => f l ω a) 4 μ) (l : ℕ) (a b : Fin k) :
    MemLp (fun ω => f l ω a * f l ω b) 2 μ := by
  -- sketch: exact memLp_two_mul_of_memLp4 (hmom l a) (hmom l b)
  --   (factor_coord_meas hmeas l a) (factor_coord_meas hmeas l b)
  exact memLp_two_mul_of_memLp4 (hmom l a) (hmom l b) (factor_coord_meas hmeas l a) (factor_coord_meas hmeas l b)

/-- `(Σ_c (f⁽ˡ⁾_c)²)²` is integrable: it expands into the products `f_c² f_d²`, each of which
is integrable by `integrable_pow_mul_pow_of_memLp4` (`2 + 2 = 4`). -/
lemma factor_sumsq_sq_integrable (hmeas : ∀ l, Measurable (f l))
    (hmom : ∀ l a, MemLp (fun ω => f l ω a) 4 μ) (l : ℕ) :
    Integrable (fun ω => (∑ c, f l ω c ^ 2) ^ 2) μ := by
  -- sketch: rewrite the square of the sum as a double sum,
  --   (∑ c, x c) ^ 2 = ∑ c, ∑ d, x c * x d   (`sq`, `Finset.sum_mul_sum`),
  -- then `integrable_finset_sum` twice, each summand by
  -- `integrable_pow_mul_pow_of_memLp4 (hmom l c) (hmom l d) (factor_coord_meas hmeas l c)
  --   (factor_coord_meas hmeas l d) 2 2 (by norm_num)`.
  have h : ∀ ω : Ω, (∑ c, f l ω c ^ 2) ^ 2 = ∑ c, ∑ d, f l ω c ^ 2 * f l ω d ^ 2 := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  have hd : Integrable (fun ω => ∑ c, ∑ d, f l ω c ^ 2 * f l ω d ^ 2) μ :=
    integrable_finset_sum _ fun c _ => integrable_finset_sum _ fun d _ =>
      integrable_pow_mul_pow_of_memLp4 (hmom l c) (hmom l d) (factor_coord_meas hmeas l c)
        (factor_coord_meas hmeas l d) 2 2 (by norm_num)
  exact hd.congr (Filter.Eventually.of_forall fun ω => (h ω).symm)

/-- The variance of one product is at most `κ_f`. -/
lemma factor_prod_variance_le (hmeas : ∀ l, Measurable (f l))
    (hmom : ∀ l a, MemLp (fun ω => f l ω a) 4 μ) {κf : ℝ}
    (h4 : ∀ l, μ[fun ω => (∑ a, f l ω a ^ 2) ^ 2] ≤ κf) (l : ℕ) (a b : Fin k) :
    variance (fun ω => f l ω a * f l ω b) μ ≤ κf := by
  -- sketch: as in `NoiseModel.avg_cross`.
  -- `variance_le_expectation_sq` bounds the variance by μ[X²] with
  -- X := fun ω => f l ω a * f l ω b (aestronglyMeasurable from `factor_coord_meas`).
  -- X² ≤ (∑ c, f l ω c ^ 2) ^ 2 pointwise by `sq_mul_le_sum_sq_sq`, X² is integrable
  -- (`memLp_two_iff_integrable_sq` applied to `factor_prod_memLp2`), and the bound is
  -- integrable by `factor_sumsq_sq_integrable`, so `integral_mono` gives
  -- μ[X²] ≤ μ[(∑ c, f l ω c ^ 2) ^ 2] ≤ κf by `h4 l`.
  have hm := (factor_coord_meas hmeas l a).mul (factor_coord_meas hmeas l b)
  refine (variance_le_expectation_sq hm.aestronglyMeasurable).trans ?_
  have hint1 : Integrable (fun ω => (f l ω a * f l ω b) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).1 (factor_prod_memLp2 hmeas hmom l a b)
  have hle : ∀ ω, (f l ω a * f l ω b) ^ 2 ≤ (∑ c, f l ω c ^ 2) ^ 2 :=
    fun ω => sq_mul_le_sum_sq_sq (f l ω) a b
  have key : μ[fun ω => (f l ω a * f l ω b) ^ 2] ≤ κf :=
    (integral_mono hint1 (factor_sumsq_sq_integrable hmeas hmom l) hle).trans (h4 l)
  exact key

/-- **Remark after Corollary 3.**  `(1/n) Σ_{l<n} f⁽ˡ⁾_a f⁽ˡ⁾_b → Σ_f(a,b)` almost surely. -/
theorem factor_entry_slln (hFact1 : Fact1_SLLN) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Sf : Matrix (Fin k) (Fin k) ℝ) (f : ℕ → Ω → Fin k → ℝ) (hmeas : ∀ l, Measurable (f l))
    (hindep : iIndepFun f μ) (hmom : ∀ l a, MemLp (fun ω => f l ω a) 4 μ)
    (hcov : ∀ l a b, μ[fun ω => f l ω a * f l ω b] = Sf a b)
    (κf : ℝ) (h4 : ∀ l, μ[fun ω => (∑ a, f l ω a ^ 2) ^ 2] ≤ κf) (a b : Fin k) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ l ∈ Finset.range n, f l ω a * f l ω b)
      atTop (𝓝 (Sf a b)) := by
  have hslln := slln_range hFact1
    (fun l => (factor_coord_meas hmeas l a).mul (factor_coord_meas hmeas l b))
    (fun l => factor_prod_memLp2 hmeas hmom l a b) (factor_prod_indep hindep a b)
    (fun l => factor_prod_variance_le hmeas hmom h4 l a b)
  have hc : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ _l ∈ Finset.range n, Sf a b) atTop
      (𝓝 (Sf a b)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp
    simp [Finset.sum_const, Finset.card_range, mul_comm]
  filter_upwards [hslln] with ω hω
  have h := hω.add hc
  rw [zero_add] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  simp only [hcov, Finset.sum_sub_distrib]
  ring

end PCError

end
