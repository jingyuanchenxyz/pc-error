import LatentError.Lemmas.Prop3
import LatentError.Lemmas.CondKernel

/-!
# Leaf lemmas for Lemma 5 (all-pairs uncorrelatedness and the per-date covariance)

In the joint model (`JointModel`), Assumption 2 holds conditionally on `σ(F)`.  Lemma 5 needs
the *unconditional* consequences:

* `JointModel.integral_Z_mul_fc`: `E[Z_{il} f⁽ᵐ⁾_a] = 0` — the factor coordinate is
  `σ(F)`-measurable, so it pulls out of `E[· | σ(F)]`, and `E[Z_{il} | σ(F)] = 0`;
* `JointModel.integral_Z_sq`: `E[Z_{il}²] = δ²_{i,l}` — the tower property and `A2_var`;
* `JointModel.integral_Z_mul_Z`: `E[Z_{il} Z_{i'l}] = 0` for `i ≠ i'` — conditional
  independence plus conditional mean zero (see `Lemmas/CondKernel.lean`);
* the expansion of `y⁽ˡ⁾ = B f⁽ˡ⁾ + z⁽ˡ⁾` into the four groups of terms.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory Matrix

noncomputable section

namespace PCError

variable {k n : ℕ} {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-! ## Integrability -/

/-- Hölder for the exponent pair `(2, 2)`: a product of square-integrable functions is
integrable. -/
lemma integrable_mul_of_memLp2 {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => f ω * g ω) μ := by
  -- sketch: `MemLp.integrable_mul` needs the instance `ENNReal.HolderTriple 2 2 1`
  -- (`2⁻¹ + 2⁻¹ = 1⁻¹`); provide it with `haveI : ENNReal.HolderTriple 2 2 1 := ⟨by simp⟩`
  -- (or `ENNReal.inv_two_add_inv_two`), then `exact hf.integrable_mul hg` after rewriting
  -- `fun ω => f ω * g ω` as `f * g` (`Pi.mul_apply`, `rfl`).
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  exact hf.integrable_mul hg

/-- `Z_{il}` has a finite fourth moment. -/
lemma JointModel.memLp_Z_four (J : JointModel k n Ω μ) (i : ℕ) (l : Fin n) :
    MemLp (J.Z i l) 4 μ := by
  -- sketch: `(integrable_norm_rpow_iff (J.Z_meas i l).aestronglyMeasurable (by norm_num)
  --   (by norm_num)).1`, after rewriting the integrand: for p = 4,
  -- ‖Z ω‖ ^ (4 : ℝ≥0∞).toReal = Z ω ^ 4 (`ENNReal.toReal_ofNat`, `Real.rpow_natCast`,
  -- `Real.norm_eq_abs`, `Even.pow_abs (by decide : Even 4)`), so the hypothesis is
  -- `J.A2_int4 i l`.
  refine (integrable_norm_rpow_iff (J.Z_meas i l).aestronglyMeasurable (by norm_num) (by norm_num)).1 ?_
  simpa [Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_natCast, Even.pow_abs (by decide : Even 4)] using J.A2_int4 i l

/-- `Z_{il}` is square integrable. -/
lemma JointModel.memLp_Z_two (J : JointModel k n Ω μ) (i : ℕ) (l : Fin n) :
    MemLp (J.Z i l) 2 μ :=
  (J.memLp_Z_four i l).mono_exponent (by norm_num)

lemma JointModel.integrable_Z_mul_fc (J : JointModel k n Ω μ) (i : ℕ) (l : Fin n) (a : Fin k)
    (m : Fin n) : Integrable (fun ω => J.Z i l ω * J.fc a m ω) μ :=
  integrable_mul_of_memLp2 (J.memLp_Z_two i l) (J.A1_memLp a m)

lemma JointModel.integrable_fc_mul (J : JointModel k n Ω μ) (a b : Fin k) (l m : Fin n) :
    Integrable (fun ω => J.fc a l ω * J.fc b m ω) μ :=
  integrable_mul_of_memLp2 (J.A1_memLp a l) (J.A1_memLp b m)

lemma JointModel.integrable_Z_mul_Z (J : JointModel k n Ω μ) (i i' : ℕ) (l : Fin n) :
    Integrable (fun ω => J.Z i l ω * J.Z i' l ω) μ :=
  integrable_mul_of_memLp2 (J.memLp_Z_two i l) (J.memLp_Z_two i' l)

/-! ## `σ(F)`-measurability of the factor coordinates -/

/-- Each factor coordinate is measurable for `σ(F)`. -/
lemma JointModel.measurable_fc_sigmaF (J : JointModel k n Ω μ) (a : Fin k) (m : Fin n) :
    Measurable[sigmaF J.fc] (J.fc a m) := by
  -- sketch: `sigmaF J.fc` is `MeasurableSpace.comap (fun ω a l => J.fc a l ω)
  -- MeasurableSpace.pi` (unfold `sigmaF`), and `J.fc a m` factors as
  -- `(fun v => v a m) ∘ (fun ω a l => J.fc a l ω)`.  So provide the comap witness directly:
  -- `fun s hs => ⟨(fun v => v a m) ⁻¹' s, (measurable_pi_apply m).comp (measurable_pi_apply a) hs,
  --   rfl⟩` — i.e. `Measurable.comp (m := MeasurableSpace.pi)
  --   ((measurable_pi_apply m).comp (measurable_pi_apply a)) (comap_measurable _)`.
  intro s hs
  refine ⟨(fun v : Fin k → Fin n → ℝ => v a m) ⁻¹' s, ?_, rfl⟩
  exact ((measurable_pi_apply m).comp (measurable_pi_apply a)) hs

lemma JointModel.stronglyMeasurable_fc_sigmaF (J : JointModel k n Ω μ) (a : Fin k) (m : Fin n) :
    StronglyMeasurable[sigmaF J.fc] (J.fc a m) :=
  (J.measurable_fc_sigmaF a m).stronglyMeasurable

/-! ## The three moment identities -/

/-- `E[Z_{il} f⁽ᵐ⁾_a] = 0` (eq. (56)). -/
lemma JointModel.integral_Z_mul_fc (J : JointModel k n Ω μ) (i : ℕ) (l : Fin n) (a : Fin k)
    (m : Fin n) : μ[fun ω => J.Z i l ω * J.fc a m ω] = 0 := by
  -- sketch: tower property.  With hm := sigmaF_le J.fc_meas,
  -- μ[Z * f] = μ[μ[Z * f | σ(F)]] (`integral_condExp hm`, reversed), and
  -- μ[Z * f | σ(F)] =ᵐ μ[Z | σ(F)] * f = 0
  -- (`condExp_mul_of_stronglyMeasurable_right (J.stronglyMeasurable_fc_sigmaF a m)`
  -- with the integrability hypotheses `J.integrable_Z_mul_fc` and
  -- `(J.memLp_Z_two i l).integrable (by norm_num)`, then `J.A2_mean i l`).
  -- Conclude with `integral_congr_ae` and `integral_zero`.
  exact integral_Z_mul_fc_eq_zero J (J.stronglyMeasurable_fc_sigmaF a m)
    (J.integrable_Z_mul_fc i l a m) ((J.memLp_Z_two i l).integrable (by norm_num))

/-- `E[Z_{il}²] = δ²_{i,l}`. -/
lemma JointModel.integral_Z_sq (J : JointModel k n Ω μ) (i : ℕ) (l : Fin n) :
    μ[fun ω => J.Z i l ω ^ 2] = J.var i l := by
  -- sketch: `integral_condExp (sigmaF_le J.fc_meas)` (reversed) turns the left side into
  -- μ[μ[Z² | σ(F)]]; rewrite with `J.A2_var i l` and take the integral of the constant
  -- (`integral_const`, `measure_univ`).  Integrability of `Z²` comes from
  -- `(J.memLp_Z_two i l)` via `memLp_two_iff_integrable_sq`.
  exact integral_Z_sq_eq_var J
    ((memLp_two_iff_integrable_sq (J.Z_meas i l).aestronglyMeasurable).1 (J.memLp_Z_two i l))

/-- `E[Z_{il} Z_{i'l}] = 0` for `i ≠ i'` (conditional independence). -/
lemma JointModel.integral_Z_mul_Z_of_ne (J : JointModel k n Ω μ) {i i' : ℕ} (l : Fin n)
    (h : i ≠ i') : μ[fun ω => J.Z i l ω * J.Z i' l ω] = 0 := by
  exact integral_Z_mul_Z_eq_zero J h (J.integrable_Z_mul_Z i i' l)
    ((J.memLp_Z_two i l).integrable (by norm_num))
    ((J.memLp_Z_two i' l).integrable (by norm_num))

/-! ## The expansion of `y⁽ˡ⁾ y⁽ˡ⁾ᵀ` -/

/-- Pure algebra: expand `(Σ_a B_{ia} x_a + z)(Σ_b B_{i'b} y_b + z')`. -/
lemma prod_expand {k : ℕ} (c d : Fin k → ℝ) (x y : Fin k → ℝ) (z z' : ℝ) :
    (∑ a, c a * x a + z) * (∑ b, d b * y b + z') =
      (∑ a, ∑ b, c a * d b * (x a * y b)) + (∑ a, c a * (x a * z')) +
        (∑ b, d b * (z * y b)) + z * z' := by
  -- sketch: `add_mul`, `mul_add`, `Finset.sum_mul_sum` for the double sum, then
  -- `Finset.mul_sum` / `Finset.sum_mul` to pull the constants inside, and `ring_nf`
  -- (or `Finset.sum_congr rfl fun _ _ => by ring`) on each group.
  have h1 : (∑ a, c a * x a) * (∑ b, d b * y b) = ∑ a, ∑ b, c a * d b * (x a * y b) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have h2 : (∑ a, c a * x a) * z' = ∑ a, c a * (x a * z') := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  have h3 : z * (∑ b, d b * y b) = ∑ b, d b * (z * y b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [add_mul, mul_add, mul_add, h1, h2, h3]
  ring

/-- The `(i, i')` entry of `Σ₀ = B Σ_f Bᵀ`. -/
lemma sig0_apply (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ)
    (i i' : Fin p) :
    Sig0 Barr Sf p i i' = ∑ a, ∑ b, Barr i a * Sf a b * Barr i' b := by
  -- sketch: unfold `Sig0` and use `Matrix.mul_apply` twice (`Bmat`/`truncRows` entries are
  -- `Barr i a` by `rfl`), then `Finset.sum_congr` with `Finset.sum_mul` to match the shape.
  simp only [Sig0, Matrix.mul_apply, Matrix.transpose_apply, truncRows, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]

end PCError

end
