import LatentError.Model

/-!
# From kernel-level conditional independence to independence under the conditional law

Mathlib defines conditional independence given a σ-algebra `m'` as *kernel* independence
with respect to `condExpKernel μ m'` (`ProbabilityTheory.iCondIndepFun`): for every finite
family of sets the product formula holds `μ`-almost everywhere, with the quantifier order
"for all sets, for almost every `ω`".  Using it pointwise needs the reverse order, "for
almost every `ω`, for all sets", which holds because the Borel σ-algebra of `ℝ` is generated
by the countable π-system of rational half-lines `Iic q`:

* `kernel_iIndepFun_ae`: for a countable family of real-valued random variables,
  `Kernel.iIndepFun f κ μ → ∀ᵐ a ∂μ, iIndepFun f (κ a)`.

This is the missing step for the cross term of Lemma 5 (`E[Z_{il} Z_{i'l}] = 0` for
`i ≠ i'`) and for `joint_to_conditional`.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Set

noncomputable section

namespace PCError

variable {α Ω ι : Type*} [mα : MeasurableSpace α] [MeasurableSpace Ω] [Countable ι]

/-- The rational half-lines pulled back along `f`: a countable π-system generating
`σ(f)`. -/
def ratPi (f : Ω → ℝ) : Set (Set Ω) := preimage f '' ⋃ q : ℚ, {Iic (q : ℝ)}

lemma mem_ratPi {f : Ω → ℝ} {s : Set Ω} :
    s ∈ ratPi f ↔ ∃ q : ℚ, s = f ⁻¹' Iic (q : ℝ) := by
  simp only [ratPi, Set.mem_image, Set.mem_iUnion, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨Iic (q : ℝ), ⟨q, rfl⟩, rfl⟩

lemma isPiSystem_ratPi (f : Ω → ℝ) : IsPiSystem (ratPi f) := by
  intro s hs t ht hst
  obtain ⟨q, rfl⟩ := mem_ratPi.1 hs
  obtain ⟨r, rfl⟩ := mem_ratPi.1 ht
  refine mem_ratPi.2 ⟨min q r, ?_⟩
  rw [← Set.preimage_inter, Set.Iic_inter_Iic]
  congr 1
  push_cast
  rfl

lemma comap_eq_generateFrom_ratPi (f : Ω → ℝ) :
    MeasurableSpace.comap f inferInstance = generateFrom (ratPi f) := by
  rw [show (inferInstance : MeasurableSpace ℝ) = borel ℝ from BorelSpace.measurable_eq,
    Real.borel_eq_generateFrom_Iic_rat, MeasurableSpace.comap_generateFrom]
  rfl

/-- **Independence from the rational half-line product formula.**  A countable family of
real-valued random variables is independent as soon as the product formula holds for the
sets `{f i ≤ q}`, `q` rational. -/
theorem iIndepFun_of_ratPi {W : Type*} [MeasurableSpace W] (ν : Measure W)
    [IsProbabilityMeasure ν] {f : ι → W → ℝ} (hf : ∀ i, Measurable (f i))
    (h : ∀ (S : Finset ι) (q : ι → ℚ),
      ν (⋂ i ∈ S, f i ⁻¹' Iic ((q i : ℝ))) = ∏ i ∈ S, ν (f i ⁻¹' Iic ((q i : ℝ)))) :
    iIndepFun f ν := by
  classical
  refine iIndepSets.iIndep (fun i => (hf i).comap_le) (fun i => ratPi (f i))
    (fun i => isPiSystem_ratPi (f i)) (fun i => comap_eq_generateFrom_ratPi (f i)) ?_
  rw [iIndepSets_iff]
  intro S sets hsets
  have hchoice : ∀ i ∈ S, ∃ q : ℚ, sets i = f i ⁻¹' Iic (q : ℝ) :=
    fun i hi => mem_ratPi.1 (hsets i hi)
  choose! q hq using hchoice
  rw [Set.iInter₂_congr fun i hi => hq i hi,
    Finset.prod_congr rfl fun i hi => by rw [hq i hi]]
  exact h S q

/-- **Reversing the quantifiers in conditional independence.**  For a countable family of
real-valued random variables, kernel independence gives independence under `κ a` for almost
every `a`. -/
theorem kernel_iIndepFun_ae {κ : Kernel α Ω} [IsMarkovKernel κ] {μ : Measure α}
    {f : ι → Ω → ℝ} (hf : ∀ i, Measurable (f i)) (h : Kernel.iIndepFun f κ μ) :
    ∀ᵐ a ∂μ, iIndepFun f (κ a) := by
  classical
  -- the rational threshold attached to `i` by a test datum `t`
  set qv : (Σ S : Finset ι, S → ℚ) → ι → ℝ := fun t i =>
    if hi : i ∈ t.1 then ((t.2 ⟨i, hi⟩ : ℚ) : ℝ) else 0 with hqv
  have key : ∀ t : Σ S : Finset ι, S → ℚ, ∀ᵐ a ∂μ,
      κ a (⋂ i ∈ t.1, f i ⁻¹' Iic (qv t i)) = ∏ i ∈ t.1, κ a (f i ⁻¹' Iic (qv t i)) := by
    intro t
    exact h t.1 (f := fun i => f i ⁻¹' Iic (qv t i))
      fun i _ => ⟨Iic (qv t i), measurableSet_Iic, rfl⟩
  filter_upwards [ae_all_iff.2 key] with a ha
  refine iIndepFun_of_ratPi _ hf ?_
  intro S q
  have h1 := ha ⟨S, fun i => q (i : ι)⟩
  have hqv : ∀ i ∈ S, qv ⟨S, fun i => q (i : ι)⟩ i = ((q i : ℝ)) := by
    intro i hi
    rw [hqv]
    simp only [dif_pos hi]
  rw [Set.iInter₂_congr fun i hi => by rw [hqv i hi],
    Finset.prod_congr rfl fun i hi => by rw [hqv i hi]] at h1
  exact h1

/-! ## Consequences for the joint model

Integrability and `σ(F)`-measurability are hypotheses here, so that this file stays
independent of `Lemmas/Lemma5Leaves.lean`. -/

section joint

open MeasureTheory ProbabilityTheory Filter

variable {k n : ℕ} {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Conditional independence of the noise array, in the pointwise form: for almost every
`ω`, the entries are independent under the conditional law `condExpKernel μ σ(F) ω`. -/
theorem JointModel.condIndep_ae (J : JointModel k n Ω μ) :
    ∀ᵐ ω ∂μ, iIndepFun (fun (il : ℕ × Fin n) => J.Z il.1 il.2)
      (condExpKernel μ (sigmaF J.fc) ω) :=
  ae_of_ae_trim _ (kernel_iIndepFun_ae (mα := sigmaF J.fc)
    (fun il => J.Z_meas il.1 il.2) J.A2_indep)

/-- `E[Z_{il} f⁽ᵐ⁾_a] = 0`: the factor coordinate pulls out of `E[· | σ(F)]`. -/
theorem integral_Z_mul_fc_eq_zero (J : JointModel k n Ω μ) {i : ℕ} {l : Fin n} {a : Fin k}
    {m : Fin n} (hfc : @StronglyMeasurable Ω ℝ _ (sigmaF J.fc) (J.fc a m))
    (hZf : Integrable (fun ω => J.Z i l ω * J.fc a m ω) μ)
    (hZ : Integrable (J.Z i l) μ) :
    μ[fun ω => J.Z i l ω * J.fc a m ω] = 0 := by
  have hm := sigmaF_le J.fc_meas
  have hpull : μ[(J.Z i l) * (J.fc a m) | sigmaF J.fc] =ᵐ[μ]
      μ[J.Z i l | sigmaF J.fc] * J.fc a m :=
    condExp_mul_of_stronglyMeasurable_right hfc hZf hZ
  have h0 : μ[(J.Z i l) * (J.fc a m) | sigmaF J.fc] =ᵐ[μ] 0 := by
    refine hpull.trans ?_
    filter_upwards [J.A2_mean i l] with ω hω
    simp [Pi.mul_apply, hω]
  calc μ[fun ω => J.Z i l ω * J.fc a m ω]
      = ∫ ω, μ[(J.Z i l) * (J.fc a m) | sigmaF J.fc] ω ∂μ := (integral_condExp hm).symm
    _ = 0 := by rw [integral_congr_ae h0]; simp

/-- `E[Z_{il}²] = δ²_{i,l}` by the tower property. -/
theorem integral_Z_sq_eq_var (J : JointModel k n Ω μ) {i : ℕ} {l : Fin n}
    (hZ2 : Integrable (fun ω => J.Z i l ω ^ 2) μ) :
    μ[fun ω => J.Z i l ω ^ 2] = J.var i l := by
  have hm := sigmaF_le J.fc_meas
  calc μ[fun ω => J.Z i l ω ^ 2]
      = ∫ ω, μ[fun ω => J.Z i l ω ^ 2 | sigmaF J.fc] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ _ω, J.var i l ∂μ := integral_congr_ae (J.A2_var i l)
    _ = J.var i l := by simp

/-- `E[Z_{il} Z_{i'l}] = 0` for `i ≠ i'`: conditional independence plus conditional mean
zero. -/
theorem integral_Z_mul_Z_eq_zero (J : JointModel k n Ω μ) {i i' : ℕ} {l : Fin n} (h : i ≠ i')
    (hZZ : Integrable (fun ω => J.Z i l ω * J.Z i' l ω) μ)
    (hZi : Integrable (J.Z i l) μ) (hZi' : Integrable (J.Z i' l) μ) :
    μ[fun ω => J.Z i l ω * J.Z i' l ω] = 0 := by
  have hm := sigmaF_le J.fc_meas
  have ha : μ[fun ω => J.Z i l ω * J.Z i' l ω | sigmaF J.fc] =ᵐ[μ]
      fun ω => ∫ y, J.Z i l y * J.Z i' l y ∂(condExpKernel μ (sigmaF J.fc) ω) :=
    condExp_ae_eq_integral_condExpKernel hm hZZ
  have hmean : ∀ᵐ ω ∂μ, ∫ y, J.Z i l y ∂(condExpKernel μ (sigmaF J.fc) ω) = 0 := by
    filter_upwards [condExp_ae_eq_integral_condExpKernel hm hZi, J.A2_mean i l] with ω e1 e2
    rw [← e1, e2]
    rfl
  have hmean' : ∀ᵐ ω ∂μ, ∫ y, J.Z i' l y ∂(condExpKernel μ (sigmaF J.fc) ω) = 0 := by
    filter_upwards [condExp_ae_eq_integral_condExpKernel hm hZi', J.A2_mean i' l] with ω e1 e2
    rw [← e1, e2]
    rfl
  have h0 : μ[fun ω => J.Z i l ω * J.Z i' l ω | sigmaF J.fc] =ᵐ[μ] 0 := by
    filter_upwards [ha, J.condIndep_ae, hmean, hmean'] with ω e1 e2 e3 e4
    rw [e1]
    have hne : ((i, l) : ℕ × Fin n) ≠ (i', l) := by simp [h]
    rw [(e2.indepFun hne).integral_fun_mul_eq_mul_integral
      (J.Z_meas i l).aestronglyMeasurable (J.Z_meas i' l).aestronglyMeasurable]
    rw [show (condExpKernel μ (sigmaF J.fc) ω)[J.Z i l] =
      ∫ y, J.Z i l y ∂(condExpKernel μ (sigmaF J.fc) ω) from rfl, e3, zero_mul]
    rfl
  calc μ[fun ω => J.Z i l ω * J.Z i' l ω]
      = ∫ ω, μ[fun ω => J.Z i l ω * J.Z i' l ω | sigmaF J.fc] ω ∂μ := (integral_condExp hm).symm
    _ = 0 := by rw [integral_congr_ae h0]; simp

end joint

end PCError

end
