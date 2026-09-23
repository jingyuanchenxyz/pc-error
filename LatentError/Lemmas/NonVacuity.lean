import LatentError.Lemmas.Easy
import LatentError.Lemmas.Spectral
import LatentError.Lemmas.ThmLeaves
import LatentError.Model

/-!
# Non-vacuity: the hypothesis bundles are inhabited

None of the 22 results depends on this file.  It exists so that no statement is vacuous:
`LoadingParams`, Assumptions 5–6 and `NoiseModel` are all satisfiable.

* loadings: `B ≡ 1`, `G_B = 1`, `δ² = 1`, `δ²_{i,l} ≡ 1`, `κ₄ = 1` (`k = 1`, `n = 2`);
* `Σ_f = G_B = 1` and `F = [1  0]`, so `K = 1` and `W₀ = diag(1/2, 0)`;
* noise: i.i.d. Rademacher signs, i.e. the infinite product of `(δ₁ + δ₋₁)/2`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory Matrix ENNReal

noncomputable section

namespace PCError

/-! ## Loadings -/

/-- `(1/p) Σ_{i<p} 1 → 1`. -/
lemma tendsto_avg_const_one :
    Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ _i ∈ Finset.range p, (1 : ℝ)) atTop (𝓝 1) := by
  -- sketch: refine tendsto_const_nhds.congr' ?_; filter_upwards [eventually_gt_atTop 0] with p hp
  -- then `Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul` and `field_simp`
  -- (the value is `(1/p) * p = 1` for `p > 0`).
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with p hp
  have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- For `k = 1` and `B ≡ 1`, the loading Gram is the identity as soon as `p > 0`. -/
lemma gBp_const_one {p : ℕ} (hp : 0 < p) :
    GBp (fun (_ : ℕ) (_ : Fin 1) => (1 : ℝ)) p = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  -- sketch: unfold `GBp`; the matrix `(Bᵀ * B)` has the single entry `∑ i : Fin p, 1 * 1 = p`
  -- (`Matrix.mul_apply`, `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`).
  -- Conclude with `Matrix.ext` (`Fin 1` is a subsingleton: `Subsingleton.elim`) and
  -- `Matrix.one_apply_eq`, then `field_simp` on `(1/p) * p = 1`.
  unfold GBp
  ext i j
  have : i = j := Subsingleton.elim i j
  subst this
  simp [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_const, Finset.card_univ, Matrix.one_apply_eq]
  field_simp
  simp [truncRows, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_const, Finset.card_univ, Matrix.one_apply_eq, Fintype.card_fin]

lemma tendsto_gBp_const_one :
    Tendsto (fun p : ℕ => GBp (fun (_ : ℕ) (_ : Fin 1) => (1 : ℝ)) p) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with p hp
  exact (gBp_const_one hp).symm

theorem loadingParams_nonempty : Nonempty (LoadingParams 1 2) :=
  ⟨{ Barr := fun _ _ => 1
     GB := 1
     δ2 := 1
     var := fun _ _ => 1
     κ4 := 1
     hk := le_rfl
     hkn := by norm_num
     var_pos := fun _ _ => one_pos
     δ2_pos := one_pos
     A3 := fun _ => tendsto_avg_const_one
     GB_posDef := Matrix.PosDef.one
     A4 := tendsto_gBp_const_one }⟩

/-! ## Assumptions 5 and 6 -/

/-- The example factor path `F = [1  0] ∈ ℝ^{1×2}`. -/
def Fex : Matrix (Fin 1) (Fin 2) ℝ := Matrix.of fun _ l => if l = 0 then 1 else 0

/-- `K(1, 1) = 1`. -/
lemma kmat_one_one : Kmat (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 = 1 := by
  -- sketch: unfold `Kmat`; `CFC.sqrt 1 = 1` (`CFC.sqrt_one`), then `Matrix.one_mul`.
  simp [Kmat]

/-- The sorted spectrum of the identity matrix is constant `1`. -/
lemma sortedEig_one {m : ℕ} : sortedEig (1 : Matrix (Fin m) (Fin m) ℝ) = fun _ => 1 := by
  rw [← Matrix.diagonal_one]
  exact sortedEig_diagonal_antitone (fun a b _ => le_refl _)

/-- Any function on `Fin 1` is strictly antitone (there are no pairs `i < j`). -/
lemma strictAnti_of_fin_one {α : Type*} [Preorder α] (g : Fin 1 → α) : StrictAnti g := by
  -- sketch: intro a b h; exact absurd h (by omega_nat) — use `Fin.lt_def` and
  -- `Fin.val_eq_zero` / `Subsingleton.elim` to derive a contradiction from `a < b`.
  intro i; simp

/-- `W₀(1, F) = diag(1/2, 0)` for the example path. -/
lemma w0_one_Fex : W0 (1 : Matrix (Fin 1) (Fin 1) ℝ) Fex = Matrix.diagonal ![1 / 2, 0] := by
  -- sketch: unfold `W0`, `Fex`; compute entrywise with `Matrix.ext`, `Matrix.smul_apply`,
  -- `Matrix.mul_apply`, `Matrix.diagonal_apply`, `Fin.sum_univ_one`/`Fin.sum_univ_two`,
  -- then `fin_cases` on the two indices and `norm_num [Matrix.one_apply]`.
  simp [W0, Fex]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_one, Fin.sum_univ_two] <;> norm_num

/-- The sorted spectrum of `diag(1/2, 0)`. -/
lemma sortedEig_diag_half : sortedEig (Matrix.diagonal ![(1 : ℝ) / 2, 0]) = ![1 / 2, 0] := by
  refine sortedEig_diagonal_antitone ?_
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

theorem assumptions56_satisfiable :
    ∃ (Sf GB : Matrix (Fin 1) (Fin 1) ℝ) (F : Matrix (Fin 1) (Fin 2) ℝ),
      Sf.PosDef ∧ GB.PosDef ∧ Assumption5 Sf GB ∧ Assumption6 GB F := by
  have h5 : Assumption5 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 := by
    constructor
    · rw [kmat_one_one, sortedEig_one]
      exact strictAnti_of_fin_one _
    · intro j
      rw [kmat_one_one, sortedEig_one]
      exact one_pos
  have h6 : Assumption6 (1 : Matrix (Fin 1) (Fin 1) ℝ) Fex := by
    have hlam : lam (1 : Matrix (Fin 1) (Fin 1) ℝ) Fex 0 = 1 / 2 := by
      rw [lam, sortedEigN, dif_pos (by norm_num), w0_one_Fex, sortedEig_diag_half]
      rfl
    refine ⟨strictAnti_of_fin_one _, fun j => ?_⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [show ((0 : Fin 1) : ℕ) = 0 from rfl, hlam]
    norm_num
  exact ⟨1, 1, Fex, Matrix.PosDef.one, Matrix.PosDef.one, h5, h6⟩

/-! ## Noise: i.i.d. Rademacher signs -/

/-- The Rademacher law `(δ₁ + δ₋₁)/2` on `ℝ`. -/
def rade : Measure ℝ := (1 / 2 : ℝ≥0∞) • (Measure.dirac 1 + Measure.dirac (-1))

instance rade_isProbabilityMeasure : IsProbabilityMeasure rade := by
  -- sketch: constructor; unfold `rade`; `Measure.smul_apply`, `Measure.add_apply`,
  -- `Measure.dirac_apply' _ MeasurableSet.univ` (or `measure_univ`), then `ENNReal` arithmetic:
  -- (1/2) * (1 + 1) = 1 (`ENNReal.div_add_div_same`, `ENNReal.two_mul_inv_two` or `simp`).
  constructor
  rw [rade]
  simp [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply', MeasurableSet.univ]
  norm_num
  rw [ENNReal.inv_two_add_inv_two]

lemma rade_integral_id : ∫ x, x ∂rade = 0 := by
  -- sketch: unfold `rade`; `integral_smul_measure`, `integral_add_measure`, `integral_dirac`
  -- give (1/2) • (1 + (-1)) = 0.  `ENNReal.toReal_div`/`smul_eq_mul` convert the scalar.
  rw [rade]
  rw [integral_smul_measure] <;> simp [integrable_dirac]
  rw [integral_add_measure] <;> simp [integrable_dirac]

lemma rade_integral_sq : ∫ x, x ^ 2 ∂rade = 1 := by
  rw [rade]
  rw [integral_smul_measure] <;> simp [integrable_dirac]
  rw [integral_add_measure] <;> simp [integrable_dirac]
  norm_num

lemma rade_integral_pow4 : ∫ x, x ^ 4 ∂rade = 1 := by
  rw [rade]
  rw [integral_smul_measure] <;> simp [integrable_dirac]
  rw [integral_add_measure] <;> simp [integrable_dirac]
  norm_num

lemma rade_memLp4 : MemLp (fun x : ℝ => x) 4 rade := by
  -- sketch: the identity is bounded by 1 on the support: use
  -- `MemLp.of_bound aestronglyMeasurable_id 1 ?_` and show `∀ᵐ x ∂rade, ‖x‖ ≤ 1`.
  -- For the a.e. bound, `rade` is supported on {1, -1}: unfold `rade` and use
  -- `ae_smul_measure`, `ae_add_measure_iff`, `ae_dirac_iff` (with the measurable set
  -- {x | ‖x‖ ≤ 1}), then `norm_num`.
  refine MemLp.of_bound measurable_id'.aestronglyMeasurable 1 ?_
  simp [rade]

/-- The i.i.d. Rademacher array on `ℕ × Fin n`. -/
def radePi (n : ℕ) : Measure (ℕ × Fin n → ℝ) := Measure.infinitePi fun _ => rade

instance radePi_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (radePi n) := by
  unfold radePi; infer_instance

lemma radePi_map_coord (n : ℕ) (il : ℕ × Fin n) :
    (radePi n).map (fun z => z il) = rade :=
  Measure.infinitePi_map_eval _ il

lemma radePi_coord_indep (n : ℕ) :
    iIndepFun (fun (il : ℕ × Fin n) (z : ℕ × Fin n → ℝ) => z il) (radePi n) := by
  -- sketch: `iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)` gives
  -- independence of `fun i ω => ω i` under `infinitePi`; that is the statement after
  -- unfolding `radePi`.
  rw [radePi]
  exact iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)

/-- Transfer an integral of one coordinate to the Rademacher law. -/
lemma radePi_integral_coord (n : ℕ) (il : ℕ × Fin n) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g rade) :
    ∫ z, g (z il) ∂(radePi n) = ∫ x, g x ∂rade := by
  have hg' : AEStronglyMeasurable g ((radePi n).map (fun z => z il)) := by
    rwa [radePi_map_coord]
  have h := integral_map (φ := fun z : ℕ × Fin n → ℝ => z il) (f := g)
    (measurable_pi_apply il).aemeasurable hg'
  rw [radePi_map_coord] at h
  exact h.symm

/-- Transfer `MemLp` of one coordinate to the Rademacher law. -/
lemma radePi_memLp_coord (n : ℕ) (il : ℕ × Fin n) {g : ℝ → ℝ} {p : ℝ≥0∞}
    (hgm : AEStronglyMeasurable g rade) (hg : MemLp g p rade) :
    MemLp (fun z => g (z il)) p (radePi n) := by
  have hg' : AEStronglyMeasurable g ((radePi n).map (fun z => z il)) := by
    rwa [radePi_map_coord]
  have := (memLp_map_measure_iff hg' (measurable_pi_apply il).aemeasurable).1
    (by rwa [radePi_map_coord])
  exact this

theorem noiseModel_nonempty (n : ℕ) :
    ∃ μ : Measure (ℕ × Fin n → ℝ), IsProbabilityMeasure μ ∧
      Nonempty (NoiseModel n (fun _ _ => 1) 1 (ℕ × Fin n → ℝ) μ) := by
  classical
  refine ⟨radePi n, inferInstance, ⟨⟨fun i l z => z (i, l), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · exact fun i l => measurable_pi_apply (i, l)
  · exact radePi_coord_indep n
  · exact fun i l => radePi_memLp_coord n (i, l) (g := fun x : ℝ => x) measurable_id'.aestronglyMeasurable rade_memLp4
  · intro i l
    rw [show (radePi n)[fun z : ℕ × Fin n → ℝ => z (i, l)] =
      ∫ z, (fun x : ℝ => x) (z (i, l)) ∂(radePi n) from rfl,
      radePi_integral_coord n (i, l) (g := fun x : ℝ => x) measurable_id'.aestronglyMeasurable]
    exact rade_integral_id
  · intro i l
    have hmean : (radePi n)[fun z : ℕ × Fin n → ℝ => z (i, l)] = 0 := by
      rw [show (radePi n)[fun z : ℕ × Fin n → ℝ => z (i, l)] =
        ∫ z, (fun x : ℝ => x) (z (i, l)) ∂(radePi n) from rfl,
        radePi_integral_coord n (i, l) (g := fun x : ℝ => x) measurable_id'.aestronglyMeasurable]
      exact rade_integral_id
    rw [variance_of_integral_eq_zero (measurable_pi_apply (i, l)).aemeasurable hmean,
      show (radePi n)[fun z : ℕ × Fin n → ℝ => z (i, l) ^ 2] =
        ∫ z, (fun x : ℝ => x ^ 2) (z (i, l)) ∂(radePi n) from rfl,
      radePi_integral_coord n (i, l) (g := fun x : ℝ => x ^ 2) (measurable_id'.pow_const 2).aestronglyMeasurable]
    exact rade_integral_sq
  · intro i l
    rw [show (radePi n)[fun z : ℕ × Fin n → ℝ => z (i, l) ^ 4] =
      ∫ z, (fun x : ℝ => x ^ 4) (z (i, l)) ∂(radePi n) from rfl,
      radePi_integral_coord n (i, l) (g := fun x : ℝ => x ^ 4) (measurable_id'.pow_const 4).aestronglyMeasurable]
    exact le_of_eq rade_integral_pow4

end PCError

end
