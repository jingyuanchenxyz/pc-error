import LatentError.Model
import LatentError.Lemmas.CondKernel

/-!
# From the joint model to the conditional reading (Section 4)

The paper reads "conditional on `F` and almost surely as `p → ∞`" as follows: for almost
every realization `F`, the convergence holds with probability one under the conditional law
of the noise array `{Z_il}` given `F`. It adds that "our path-conditional statements
upgrade automatically to unconditional ones by the tower property".

The results in `Main.lean` and `Appendix.lean` are stated for a `NoiseModel`, which
models that conditional law directly. This file states the two links back to the paper's
joint Assumptions 1–2 (`JointModel`):

1. `joint_to_conditional`: for almost every factor path `F`, the regular conditional law
   of the noise array given `F` makes the coordinate projections a `NoiseModel` with the
   same variances `δ²_{i,l}` and fourth-moment bound `κ₄`.
2. `tower_upgrade`: a measurable property of `(F, Z)` that holds almost surely under the
   conditional law, for almost every `F`, holds almost surely under the joint law.

Added 2026-09-17 after the statement-fidelity review (`notes/statement-fidelity.md`, §1).
-/

open MeasureTheory ProbabilityTheory

noncomputable section

set_option linter.unusedVariables false

namespace PCError

variable {k n : ℕ} {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The factor path `F` as one random element of `Fin k → Fin n → ℝ`. -/
abbrev JointModel.Fvec (J : JointModel k n Ω μ) : Ω → (Fin k → Fin n → ℝ) :=
  fun ω a l => J.fc a l ω

/-- The whole noise array `{Z_il}` as one random element of `ℕ × Fin n → ℝ`. -/
abbrev JointModel.Zvec (J : JointModel k n Ω μ) : Ω → (ℕ × Fin n → ℝ) :=
  fun ω il => J.Z il.1 il.2 ω

/-- **Section 4, the conditional reading.**  Under Assumptions 1–2 (joint form), for
almost every factor path `F`, the conditional law of the noise array given `F` satisfies
Assumption 2 in the form of `NoiseModel`, with the coordinate projections `z ↦ z (i, l)`
as the noise entries. -/
theorem joint_to_conditional (J : JointModel k n Ω μ) :
    ∀ᵐ x ∂(μ.map J.Fvec),
      ∃ N : NoiseModel n J.var J.κ4 (ℕ × Fin n → ℝ) (condDistrib J.Zvec J.Fvec μ x),
        ∀ i l, N.Z i l = fun z => z (i, l) := by
  classical
  have hFm : Measurable J.Fvec :=
    measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun l => J.fc_meas a l
  have hZm : Measurable J.Zvec := measurable_pi_iff.2 fun il => J.Z_meas il.1 il.2
  have hc : ∀ il : ℕ × Fin n, Measurable (fun z : ℕ × Fin n → ℝ => z il) :=
    fun il => measurable_pi_apply il
  -- fourth moments, hence square integrability, of the noise entries
  have hZ4 : ∀ (i : ℕ) (l : Fin n), MemLp (J.Z i l) 4 μ := by
    intro i l
    refine (integrable_norm_rpow_iff (J.Z_meas i l).aestronglyMeasurable (by norm_num)
      (by norm_num)).1 ?_
    simpa [Real.norm_eq_abs, Real.rpow_natCast, Even.pow_abs (by decide : Even 4)] using
      J.A2_int4 i l
  have hZ2 : ∀ (i : ℕ) (l : Fin n), MemLp (J.Z i l) 2 μ :=
    fun i l => (hZ4 i l).mono_exponent (by norm_num)
  -- the rational thresholds attached to a test datum
  set qval : (Σ S : Finset (ℕ × Fin n), S → ℚ) → (ℕ × Fin n) → ℝ := fun t il =>
    if hil : il ∈ t.1 then ((t.2 ⟨il, hil⟩ : ℚ) : ℝ) else 0 with hqval
  -- the conditional law as a kernel in the factor path
  set K := condDistrib J.Zvec J.Fvec μ with hK
  -- (A) independence of the coordinates under `K x`, for a.e. `x`
  have hsig : MeasurableSpace.comap J.Fvec MeasurableSpace.pi = sigmaF J.fc := rfl
  have hindep : ∀ᵐ x ∂(μ.map J.Fvec), iIndepFun (fun (il : ℕ × Fin n) (z : ℕ × Fin n → ℝ) => z il)
      (K x) := by
    have key : ∀ t : Σ S : Finset (ℕ × Fin n), S → ℚ, ∀ᵐ x ∂(μ.map J.Fvec),
        K x (⋂ il ∈ t.1, (fun z : ℕ × Fin n → ℝ => z il) ⁻¹' Set.Iic (qval t il)) =
          ∏ il ∈ t.1, K x ((fun z : ℕ × Fin n → ℝ => z il) ⁻¹' Set.Iic (qval t il)) := by
      intro t
      set A : (ℕ × Fin n) → Set (ℕ × Fin n → ℝ) := fun il =>
        (fun z : ℕ × Fin n → ℝ => z il) ⁻¹' Set.Iic (qval t il) with hA
      have hsets : ∀ il, MeasurableSet (A il) := fun il => (hc il) measurableSet_Iic
      have hbig : MeasurableSet (⋂ il ∈ t.1, A il) :=
        MeasurableSet.biInter (Set.to_countable _) fun il _ => hsets il
      have hmeasset : MeasurableSet {x | K x (⋂ il ∈ t.1, A il) = ∏ il ∈ t.1, K x (A il)} := by
        refine measurableSet_eq_fun (Kernel.measurable_coe K hbig) ?_
        exact Finset.measurable_prod _ fun il _ => Kernel.measurable_coe K (hsets il)
      rw [ae_map_iff hFm.aemeasurable hmeasset]
      -- on the `ω` side: `K (F ω)` is the `Z`-image of the conditional-expectation kernel
      have hcd : ∀ s : Set (ℕ × Fin n → ℝ), MeasurableSet s →
          ∀ᵐ ω ∂μ, K (J.Fvec ω) s = condExpKernel μ (sigmaF J.fc) ω (J.Zvec ⁻¹' s) := by
        intro s hs
        filter_upwards [condDistrib_apply_ae_eq_condExpKernel_map hZm hFm hs] with ω hω
        rw [hK, hω, Kernel.map_apply' _ hZm _ hs, hsig]
      have hprod : ∀ᵐ ω ∂μ, condExpKernel μ (sigmaF J.fc) ω (⋂ il ∈ t.1, J.Zvec ⁻¹' A il) =
          ∏ il ∈ t.1, condExpKernel μ (sigmaF J.fc) ω (J.Zvec ⁻¹' A il) :=
        ae_of_ae_trim _ (J.A2_indep t.1 (f := fun il => J.Zvec ⁻¹' A il)
          fun il _ => ⟨Set.Iic (qval t il), measurableSet_Iic, rfl⟩)
      have hfac : ∀ᵐ ω ∂μ, ∀ il ∈ t.1,
          K (J.Fvec ω) (A il) = condExpKernel μ (sigmaF J.fc) ω (J.Zvec ⁻¹' A il) := by
        rw [Filter.eventually_all_finset]
        intro il _
        filter_upwards [hcd _ (hsets il)] with ω hω using hω
      filter_upwards [hcd _ hbig, hprod, hfac] with ω e1 e2 e3
      rw [e1, Set.preimage_iInter₂, e2]
      exact Finset.prod_congr rfl fun il hil => (e3 il hil).symm
    filter_upwards [ae_all_iff.2 key] with x hx
    refine iIndepFun_of_ratPi _ hc ?_
    intro S q
    have h1 := hx ⟨S, fun i => q (i : ℕ × Fin n)⟩
    have hq : ∀ il ∈ S, qval ⟨S, fun i => q (i : ℕ × Fin n)⟩ il = ((q il : ℝ)) := by
      intro il hil
      rw [hqval]
      simp only [dif_pos hil]
    rw [Set.iInter₂_congr fun il hil => by rw [hq il hil],
      Finset.prod_congr rfl fun il hil => by rw [hq il hil]] at h1
    exact h1
  -- (B) the fourth moment is finite under `K x`
  have hmemLp4 : ∀ᵐ x ∂(μ.map J.Fvec), ∀ (i : ℕ) (l : Fin n),
      MemLp (fun z : ℕ × Fin n → ℝ => z (i, l)) 4 (K x) := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun l => ?_
    have hmap : Integrable (fun p : (Fin k → Fin n → ℝ) × (ℕ × Fin n → ℝ) => p.2 (i, l) ^ 4)
        (μ.map fun ω => (J.Fvec ω, J.Zvec ω)) :=
      (integrable_map_measure (by fun_prop) (hFm.prodMk hZm).aemeasurable).2 (J.A2_int4 i l)
    filter_upwards [hmap.condDistrib_ae_map hZm.aemeasurable] with x hx
    refine (integrable_norm_rpow_iff (hc (i, l)).aestronglyMeasurable (by norm_num)
      (by norm_num)).1 ?_
    simpa [Real.norm_eq_abs, Real.rpow_natCast, Even.pow_abs (by decide : Even 4)] using hx
  -- (C) the three moment identities, transferred from `ω` to `x`
  have hmoment : ∀ (g : ℝ → ℝ), Measurable g → ∀ (i : ℕ) (l : Fin n),
      Integrable (fun ω => g (J.Z i l ω)) μ →
      μ[fun ω => g (J.Z i l ω) | sigmaF J.fc] =ᵐ[μ]
        fun ω => ∫ z, g (z (i, l)) ∂(K (J.Fvec ω)) := by
    intro g hg i l hint
    have hf : StronglyMeasurable (fun z : ℕ × Fin n → ℝ => g (z (i, l))) :=
      (hg.comp (measurable_pi_apply (i, l))).stronglyMeasurable
    exact condExp_ae_eq_integral_condDistrib hFm hZm.aemeasurable hf hint
  have hsm : ∀ (g : ℝ → ℝ), Measurable g →
      ∀ (i : ℕ) (l : Fin n), Measurable fun x => ∫ z, g (z (i, l)) ∂(K x) := by
    intro g hg i l
    have hf : StronglyMeasurable
        (fun p : (Fin k → Fin n → ℝ) × (ℕ × Fin n → ℝ) => g (p.2 (i, l))) :=
      (hg.comp ((measurable_pi_apply (i, l)).comp measurable_snd)).stronglyMeasurable
    exact (MeasureTheory.StronglyMeasurable.integral_condDistrib (X := J.Fvec)
      (Y := J.Zvec) (μ := μ) hf).measurable
  have hmean : ∀ᵐ x ∂(μ.map J.Fvec), ∀ (i : ℕ) (l : Fin n), ∫ z, z (i, l) ∂(K x) = 0 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun l => ?_
    have hz : (fun ω => ∫ z, z (i, l) ∂(K (J.Fvec ω))) =ᵐ[μ] 0 :=
      (hmoment (fun x => x) measurable_id' i l ((hZ2 i l).integrable (by norm_num))).symm.trans
        (J.A2_mean i l)
    rw [ae_map_iff hFm.aemeasurable
      (measurableSet_eq_fun (hsm (fun x => x) measurable_id' i l) measurable_const)]
    filter_upwards [hz] with ω hω using hω
  have hsq : ∀ᵐ x ∂(μ.map J.Fvec), ∀ (i : ℕ) (l : Fin n),
      ∫ z, z (i, l) ^ 2 ∂(K x) = J.var i l := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun l => ?_
    have hint : Integrable (fun ω => J.Z i l ω ^ 2) μ :=
      (memLp_two_iff_integrable_sq (J.Z_meas i l).aestronglyMeasurable).1 (hZ2 i l)
    have hz : (fun ω => ∫ z, z (i, l) ^ 2 ∂(K (J.Fvec ω))) =ᵐ[μ] fun _ => J.var i l :=
      (hmoment (fun x => x ^ 2) (measurable_id'.pow_const 2) i l hint).symm.trans (J.A2_var i l)
    rw [ae_map_iff hFm.aemeasurable
      (measurableSet_eq_fun (hsm (fun x => x ^ 2) (measurable_id'.pow_const 2) i l)
        measurable_const)]
    filter_upwards [hz] with ω hω using hω
  have hfourth : ∀ᵐ x ∂(μ.map J.Fvec), ∀ (i : ℕ) (l : Fin n),
      ∫ z, z (i, l) ^ 4 ∂(K x) ≤ J.κ4 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun l => ?_
    have hz : ∀ᵐ ω ∂μ, ∫ z, z (i, l) ^ 4 ∂(K (J.Fvec ω)) ≤ J.κ4 := by
      filter_upwards [(hmoment (fun x => x ^ 4) (measurable_id'.pow_const 4) i l
        (J.A2_int4 i l)).symm, J.A2_fourth i l] with ω e1 e2
      rw [e1]
      exact e2
    rw [ae_map_iff hFm.aemeasurable
      (measurableSet_le (hsm (fun x => x ^ 4) (measurable_id'.pow_const 4) i l)
        measurable_const)]
    filter_upwards [hz] with ω hω using hω
  -- assemble the `NoiseModel`
  filter_upwards [hindep, hmemLp4, hmean, hsq, hfourth] with x h1 h2 h3 h4 h5
  refine ⟨⟨fun i l z => z (i, l), fun i l => hc (i, l), h1, fun i l => h2 i l,
    fun i l => h3 i l, fun i l => ?_, fun i l => h5 i l⟩, fun i l => rfl⟩
  rw [variance_of_integral_eq_zero (hc (i, l)).aemeasurable (h3 i l)]
  exact h4 i l

/-- **Section 4, the tower property.**  A measurable property of the pair `(F, Z)` that
holds almost surely under the conditional law of `Z` given `F`, for almost every `F`,
holds almost surely under the joint law. -/
theorem tower_upgrade (J : JointModel k n Ω μ)
    {S : Set ((Fin k → Fin n → ℝ) × (ℕ × Fin n → ℝ))} (hS : MeasurableSet S)
    (h : ∀ᵐ x ∂(μ.map J.Fvec), ∀ᵐ z ∂(condDistrib J.Zvec J.Fvec μ x), (x, z) ∈ S) :
    ∀ᵐ ω ∂μ, (J.Fvec ω, J.Zvec ω) ∈ S := by
  have hF : Measurable J.Fvec :=
    measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun l => J.fc_meas a l
  have hZ : Measurable J.Zvec := measurable_pi_iff.2 fun il => J.Z_meas il.1 il.2
  have h1 : ∀ᵐ q ∂((μ.map J.Fvec) ⊗ₘ condDistrib J.Zvec J.Fvec μ), q ∈ S :=
    (Measure.ae_compProd_iff hS).2 h
  rw [compProd_map_condDistrib hZ.aemeasurable] at h1
  exact (ae_map_iff (hF.prodMk hZ).aemeasurable hS).1 h1

end PCError

end
