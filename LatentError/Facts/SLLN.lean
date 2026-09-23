import LatentError.Facts.Kronecker
import LatentError.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.BorelCantelli

/-!
# Fact 1: Kolmogorov's strong law for independent, non-identically distributed summands

We prove `Fact1_SLLN` (stated in `LatentError/Basic.lean`) rather than assume it.  The proof
is the classical one:

1. **Khintchine–Kolmogorov** (`ae_tendsto_sum_of_summable_variance`): if `Y i` are
   independent, centered and square integrable with `∑ Var(Y i) < ∞`, then `∑ Y i` converges
   almost surely.  The partial sums form an `L²`-bounded martingale for the natural
   filtration (`iIndepFun.condExp_natural_ae_eq_of_lt` gives the martingale property, and
   `IndepFun.variance_sum` the second-moment bound), so Mathlib's almost-everywhere
   martingale convergence theorem `Submartingale.exists_ae_tendsto_of_bdd` applies.
2. **Kronecker's lemma** (`LatentError/Facts/Kronecker.lean`) turns the convergence of
   `∑ (X i - E X i)/i` into `(1/p) ∑_{i ≤ p} (X i - E X i) → 0`.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace PCError

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A second-moment bound gives an `L¹` bound: `‖f‖₁ ≤ √C` when `E[f²] ≤ C`. -/
lemma eLpNorm_one_le_of_sq_le {f : Ω → ℝ} (hf : MemLp f 2 μ) {C : ℝ}
    (h : ∫ ω, f ω ^ 2 ∂μ ≤ C) : eLpNorm f 1 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
  have habs : MemLp (fun ω => |f ω|) 2 μ := hf.abs
  have hint : Integrable f μ := hf.integrable one_le_two
  have hsq : ∫ ω, |f ω| ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp [sq_abs]
  -- `0 ≤ Var |f| = E[f²] - (E|f|)²`
  have hvar := variance_nonneg (fun ω => |f ω|) μ
  rw [variance_eq_sub habs] at hvar
  have h1 : (∫ ω, |f ω| ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂μ := by
    have e : μ[(fun ω => |f ω|) ^ 2] = ∫ ω, f ω ^ 2 ∂μ := by
      rw [← hsq]
      rfl
    rw [e] at hvar
    linarith
  have hnn : 0 ≤ ∫ ω, |f ω| ∂μ := integral_nonneg fun ω => abs_nonneg _
  have hC0 : 0 ≤ C := le_trans (le_trans (sq_nonneg _) h1) h
  have hle : ∫ ω, |f ω| ∂μ ≤ Real.sqrt C := by
    nlinarith [Real.sq_sqrt hC0, Real.sqrt_nonneg C, hnn, h1.trans h]
  calc eLpNorm f 1 μ = ENNReal.ofReal (∫ ω, ‖f ω‖ ∂μ) := by
        rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hint]
    _ ≤ ENNReal.ofReal (Real.sqrt C) := by
        refine ENNReal.ofReal_le_ofReal ?_
        simpa [Real.norm_eq_abs] using hle

/-- **Khintchine–Kolmogorov convergence theorem.**  A series of independent, centered,
square-integrable random variables with summable variances converges almost surely. -/
theorem ae_tendsto_sum_of_summable_variance {Y : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (Y i))
    (hL2 : ∀ i, MemLp (Y i) 2 μ) (hindep : iIndepFun Y μ) (hmean : ∀ i, μ[Y i] = 0)
    (hsum : Summable fun i => variance (Y i) μ) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun p => ∑ i ∈ Finset.range p, Y i ω) atTop (𝓝 c) := by
  classical
  have hsm : ∀ i, StronglyMeasurable (Y i) := fun i => (hmeas i).stronglyMeasurable
  set ℱ : Filtration ℕ ‹MeasurableSpace Ω› := Filtration.natural Y hsm with hℱ
  set M : ℕ → Ω → ℝ := fun p => ∑ i ∈ Finset.range (p + 1), Y i with hM
  have hYint : ∀ i, Integrable (Y i) μ := fun i => (hL2 i).integrable one_le_two
  have hint : ∀ p, Integrable (M p) μ := fun p =>
    integrable_finset_sum' _ fun i _ => hYint i
  -- the partial sums are adapted to the natural filtration
  have hadp : StronglyAdapted ℱ M := by
    intro p
    refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
    refine (Filtration.stronglyAdapted_natural hsm i).mono ?_
    exact ℱ.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  -- and form a martingale: the increment has conditional mean zero
  have hstep : ∀ p, M p ≤ᵐ[μ] μ[M (p + 1) | ℱ p] := by
    intro p
    have hsplit : M (p + 1) = M p + Y (p + 1) := by
      simp [hM, Finset.sum_range_succ]
    have h1 : μ[M (p + 1) | ℱ p] =ᵐ[μ] μ[M p | ℱ p] + μ[Y (p + 1) | ℱ p] := by
      rw [hsplit]
      exact condExp_add (hint p) (hYint (p + 1)) _
    have h2 : μ[M p | ℱ p] = M p :=
      condExp_of_stronglyMeasurable (ℱ.le p) (hadp p) (hint p)
    have h3 : μ[Y (p + 1) | ℱ p] =ᵐ[μ] fun _ => μ[Y (p + 1)] :=
      hindep.condExp_natural_ae_eq_of_lt hsm (Nat.lt_succ_self p)
    filter_upwards [h1, h3] with ω e1 e3
    rw [e1]
    simp only [Pi.add_apply, h2, e3, hmean, add_zero]
    exact le_rfl
  -- second moments are bounded by the total variance
  have hvar_nonneg : ∀ i, 0 ≤ variance (Y i) μ := fun i => variance_nonneg _ _
  have hbound : ∀ p, ∫ ω, M p ω ^ 2 ∂μ ≤ ∑' i, variance (Y i) μ := by
    intro p
    have hMapp : ∀ ω, M p ω = ∑ i ∈ Finset.range (p + 1), Y i ω := by
      intro ω; simp [hM]
    have hmean_M : μ[M p] = 0 := by
      rw [integral_congr_ae (Eventually.of_forall hMapp),
        integral_finset_sum _ fun i _ => hYint i]
      exact Finset.sum_eq_zero fun i _ => hmean i
    have hMmeas : AEMeasurable (M p) μ :=
      ((integrable_finset_sum' _ fun i _ => hYint i).1).aemeasurable
    have hsum_var : variance (M p) μ = ∑ i ∈ Finset.range (p + 1), variance (Y i) μ := by
      have hpair : Set.Pairwise (↑(Finset.range (p + 1)) : Set ℕ)
          fun i j => IndepFun (Y i) (Y j) μ := fun i _ j _ hij => hindep.indepFun hij
      exact IndepFun.variance_sum (X := Y) (s := Finset.range (p + 1)) (fun i _ => hL2 i) hpair
    rw [← variance_of_integral_eq_zero hMmeas hmean_M, hsum_var]
    exact hsum.sum_le_tsum _ (fun i _ => hvar_nonneg i)
  -- hence the martingale is L¹-bounded, and converges almost everywhere
  have hL1 : ∀ p, eLpNorm (M p) 1 μ ≤ ENNReal.ofReal (Real.sqrt (∑' i, variance (Y i) μ)) := by
    intro p
    exact eLpNorm_one_le_of_sq_le (memLp_finset_sum' _ fun i _ => hL2 i) (hbound p)
  have hsubm : Submartingale M ℱ μ := submartingale_nat hadp hint hstep
  have hconv := hsubm.exists_ae_tendsto_of_bdd hL1
  -- convert from `M p = ∑_{i < p+1}` back to `∑_{i < p}`
  filter_upwards [hconv] with ω hω
  obtain ⟨c, hc⟩ := hω
  refine ⟨c, ?_⟩
  rw [← tendsto_add_atTop_iff_nat (f := fun p => ∑ i ∈ Finset.range p, Y i ω) 1]
  simpa [hM] using hc

/-! ## Fact 1 -/

lemma sum_Icc_one_eq_sum_range (p : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 p, f i = ∑ i ∈ Finset.range p, f (i + 1) := by
  have h : Finset.Icc 1 p = Finset.Ico 1 (p + 1) := by
    ext i
    simp [Nat.lt_succ_iff]
  rw [h, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

lemma sum_range_succ_eq_sum_Icc (p : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0) :
    ∑ i ∈ Finset.range (p + 1), f i = ∑ i ∈ Finset.Icc 1 p, f i := by
  rw [Finset.sum_range_succ', h0, add_zero, sum_Icc_one_eq_sum_range]

/-- **Fact 1, proved.**  Kolmogorov's strong law for independent, non-identically distributed
summands: under Kolmogorov's series condition `∑ Var(Xᵢ)/i² < ∞`, the centered averages tend
to zero almost surely. -/
theorem fact1_slln : Fact1_SLLN := by
  intro Ω _ μ _ X hmeas hL2 hindep hsummable
  set Y : ℕ → Ω → ℝ := fun i ω => (X i ω - μ[X i]) / i with hY
  have hXint : ∀ i, Integrable (X i) μ := fun i => (hL2 i).integrable one_le_two
  have hYmeas : ∀ i, Measurable (Y i) := fun i => ((hmeas i).sub measurable_const).div_const _
  have hYL2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    have h := ((hL2 i).sub (memLp_const (μ[X i]))).const_mul ((i : ℝ)⁻¹)
    refine h.ae_eq ?_
    filter_upwards with ω
    show ((i : ℝ)⁻¹ * (X i ω - μ[X i])) = (X i ω - μ[X i]) / (i : ℝ)
    ring
  have hYindep : iIndepFun Y μ := by
    have := hindep.comp (β := fun _ : ℕ => ℝ) (γ := fun _ : ℕ => ℝ)
      (fun (i : ℕ) (x : ℝ) => (x - μ[X i]) / (i : ℝ))
      (fun i => (measurable_id.sub_const _).div_const _)
    exact this
  have hYmean : ∀ i, μ[Y i] = 0 := by
    intro i
    show ∫ ω, (X i ω - μ[X i]) / (i : ℝ) ∂μ = 0
    rw [integral_div, integral_sub (hXint i) (integrable_const _)]
    simp
  have hYvar : ∀ i, variance (Y i) μ = variance (X i) μ / (i : ℝ) ^ 2 := by
    intro i
    have h1 : Y i = fun ω => (X i ω - μ[X i]) * (1 / (i : ℝ)) := by
      funext ω
      rw [hY]
      ring
    rw [h1, variance_mul_const, variance_sub_const (hL2 i).aestronglyMeasurable]
    ring
  have hYsum : Summable fun i => variance (Y i) μ :=
    hsummable.congr fun i => (hYvar i).symm
  filter_upwards [ae_tendsto_sum_of_summable_variance hYmeas hYL2 hYindep hYmean hYsum] with ω hω
  obtain ⟨c, hc⟩ := hω
  -- the partial sums over `Icc 1 p` converge as well
  have hshift : Tendsto (fun p => ∑ i ∈ Finset.range (p + 1), Y i ω) atTop (𝓝 c) :=
    hc.comp (tendsto_add_atTop_nat 1)
  have hY0 : Y 0 ω = 0 := by
    show (X 0 ω - μ[X 0]) / ((0 : ℕ) : ℝ) = 0
    simp
  have hIcc : Tendsto (fun p => ∑ i ∈ Finset.Icc 1 p, (X i ω - μ[X i]) / i) atTop (𝓝 c) := by
    refine hshift.congr fun p => ?_
    exact sum_range_succ_eq_sum_Icc p (fun i => Y i ω) hY0
  exact kronecker hIcc

end PCError
