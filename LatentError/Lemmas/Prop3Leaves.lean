import LatentError.Lemmas.Prop3

/-!
# Leaf lemmas for Proposition 3

Small goals for the local harness (`harness/prove.py --all`); hints are in comments.
They feed:
* (a) entries of `ZᵀZ/(np)` and matrix limits from entrywise limits;
* (b) `BᵀZ/p → 0` from Lemma 4 applied to the normalized loading columns;
* (c) the four-term expansion of `W⁽ᵖ⁾`;
* (d) the bulk average `ℓ⁽ᵖ⁾` and traces.
-/

open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder

noncomputable section

namespace PCError

variable {k n : ℕ}

/-! ## Entries -/

lemma truncRows_transpose_mul_apply {c : ℕ} (A : ℕ → Fin c → ℝ) (p : ℕ) (l m : Fin c) :
    ((truncRows A p)ᵀ * truncRows A p) l m = ∑ i ∈ Finset.range p, A i l * A i m := by
  -- hint: simp only [Matrix.mul_apply, Matrix.transpose_apply, truncRows, Matrix.of_apply];
  -- exact Fin.sum_univ_eq_sum_range (fun i => A i l * A i m) p
  simp only [Matrix.mul_apply, Matrix.transpose_apply, truncRows, Matrix.of_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => A i l * A i m) p

lemma transpose_mul_truncRows_apply {p c : ℕ} (b : Matrix (Fin p) (Fin k) ℝ)
    (A : ℕ → Fin c → ℝ) (j : Fin k) (l : Fin c) :
    (bᵀ * truncRows A p) j l = ∑ i : Fin p, b i j * A i l := by
  -- hint: simp [Matrix.mul_apply, truncRows]
  simp [Matrix.mul_apply, truncRows, Matrix.transpose_apply]

lemma one_div_mul_eq (n p : ℕ) (s : ℝ) :
    (1 / ((n : ℝ) * p)) * s = (1 / (n : ℝ)) * ((1 / (p : ℝ)) * s) := by
  -- hint: ring
  simp only [one_div, mul_inv]
  ring

lemma smul_one_apply_fin {m : ℕ} (c : ℝ) (l l' : Fin m) :
    (c • (1 : Matrix (Fin m) (Fin m) ℝ)) l l' = if l = l' then c else 0 := by
  -- hint: simp [Matrix.one_apply]
  simp [Matrix.one_apply, smul_eq_mul]

lemma norm_colVec_sq_eq {p : ℕ} (M : Matrix (Fin p) (Fin k) ℝ) (j : Fin k) :
    ‖colVec M j‖ ^ 2 = (Mᵀ * M) j j := by
  -- hint: rw [← real_inner_self_eq_norm_sq, ← sum_mul_eq_inner_colVec]; simp [Matrix.mul_apply]
  rw [← real_inner_self_eq_norm_sq, ← sum_mul_eq_inner_colVec]; simp [Matrix.mul_apply]

lemma gBp_apply_mul (Barr : ℕ → Fin k → ℝ) (p : ℕ) (hp : 0 < p) (j : Fin k) :
    GBp Barr p j j * p = ‖colVec (Bmat Barr p) j‖ ^ 2 := by
  -- hint: rw [norm_colVec_sq_eq]; simp only [GBp, Matrix.smul_apply, smul_eq_mul];
  -- have : (p : ℝ) ≠ 0 := by positivity; field_simp
  rw [norm_colVec_sq_eq]
  simp only [GBp, Matrix.smul_apply, smul_eq_mul]
  have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  field_simp

/-! ## Limits -/

lemma tendsto_matrix_of_entries {ι : Type*} {L : Filter ι} {a b : ℕ}
    {M : ι → Matrix (Fin a) (Fin b) ℝ} {M0 : Matrix (Fin a) (Fin b) ℝ}
    (h : ∀ i j, Tendsto (fun t => M t i j) L (𝓝 (M0 i j))) : Tendsto M L (𝓝 M0) := by
  -- hint: exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j
  exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j

lemma ae_forall_fin {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {a b : ℕ}
    {P : Fin a → Fin b → Ω → Prop} (h : ∀ i j, ∀ᵐ ω ∂μ, P i j ω) :
    ∀ᵐ ω ∂μ, ∀ i j, P i j ω := by
  -- hint: rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact h i
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  exact h i

lemma tendsto_trace {ι : Type*} {L : Filter ι} {m : ℕ} {M : ι → Matrix (Fin m) (Fin m) ℝ}
    {M0 : Matrix (Fin m) (Fin m) ℝ} (h : Tendsto M L (𝓝 M0)) :
    Tendsto (fun t => (M t).trace) L (𝓝 M0.trace) := by
  -- hint: exact (continuous_id.matrix_trace.tendsto M0).comp h
  exact (continuous_id.matrix_trace.tendsto M0).comp h

lemma tendsto_bulk_avg {ι : Type*} {L : Filter ι} {a : ι → ℝ} {f : ι → ℕ → ℝ}
    {a0 : ℝ} {f0 : ℕ → ℝ} (c : ℝ) (ha : Tendsto a L (𝓝 a0))
    (hf : ∀ i, Tendsto (fun t => f t i) L (𝓝 (f0 i))) :
    Tendsto (fun t => (a t - ∑ i ∈ Finset.range k, f t i) / c) L
      (𝓝 ((a0 - ∑ i ∈ Finset.range k, f0 i) / c)) := by
  -- hint: exact (ha.sub (tendsto_finset_sum _ fun i _ => hf i)).div_const c
  exact (ha.sub (tendsto_finset_sum _ fun i _ => hf i)).div_const c

lemma tendsto_norm_div_sqrt {r : ℕ → ℝ} {G : ℝ} (hr : ∀ p, 0 ≤ r p)
    (h : Tendsto (fun p : ℕ => r p ^ 2 / p) atTop (𝓝 G)) :
    Tendsto (fun p : ℕ => r p / Real.sqrt p) atTop (𝓝 (Real.sqrt G)) := by
  -- hint: refine h.sqrt.congr' (Eventually.of_forall fun p => ?_);
  -- rw [Real.sqrt_div' _ (Nat.cast_nonneg p), Real.sqrt_sq (hr p)]
  refine h.sqrt.congr' (Eventually.of_forall fun p => ?_);
  rw [Real.sqrt_div' _ (Nat.cast_nonneg p), Real.sqrt_sq (hr p)]

lemma tendsto_div_of_normalized {S r : ℕ → ℝ} {g : ℝ}
    (hr : ∀ᶠ p in atTop, r p ≠ 0)
    (h1 : Tendsto (fun p : ℕ => S p / r p / Real.sqrt p) atTop (𝓝 0))
    (h2 : Tendsto (fun p : ℕ => r p / Real.sqrt p) atTop (𝓝 g)) :
    Tendsto (fun p : ℕ => S p / p) atTop (𝓝 0) := by
  -- hint: have h3 := h1.mul h2; rw [zero_mul] at h3; refine h3.congr' ?_;
  -- filter_upwards [hr, eventually_gt_atTop 0] with p hp hp0;
  -- have hs : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg p);
  -- have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp0);
  -- rw [← hs]; field_simp
  have h3 := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [hr, eventually_gt_atTop 0] with p hp hp0
  have hs : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp0)
  rw [← hs]
  field_simp
  simp

lemma norm_inv_smul_self {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) (hv : v ≠ 0) :
    ‖‖v‖⁻¹ • v‖ = 1 := by
  -- hint: exact norm_smul_inv_norm hv
  exact norm_smul_inv_norm hv

lemma sum_inv_smul_mul {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) (z : Fin m → ℝ) :
    ∑ i, (‖v‖⁻¹ • v) i * z i = (∑ i, v i * z i) / ‖v‖ := by
  -- hint: simp only [PiLp.smul_apply, smul_eq_mul]; rw [Finset.sum_div];
  -- refine Finset.sum_congr rfl fun i _ => ?_; ring
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## The four-term expansion of `W⁽ᵖ⁾` -/

lemma wdual_expand (Barr : ℕ → Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (Zarr : ℕ → Fin n → ℝ) (p : ℕ) :
    Wdual Barr F Zarr p =
      W0 (GBp Barr p) F
      + (1 / (n : ℝ)) • (Fᵀ * ((1 / (p : ℝ)) • ((Bmat Barr p)ᵀ * truncRows Zarr p)))
      + ((1 / (n : ℝ)) • (Fᵀ * ((1 / (p : ℝ)) • ((Bmat Barr p)ᵀ * truncRows Zarr p))))ᵀ
      + (1 / (n : ℝ)) • ((1 / (p : ℝ)) • ((truncRows Zarr p)ᵀ * truncRows Zarr p)) := by
  -- hint: simp only [Wdual, Ymat, W0, GBp, Matrix.transpose_add, Matrix.transpose_mul,
  --   Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
  --   Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, smul_add];
  -- then `rw [one_div_mul_one_div]` style rewriting of scalars: the scalar in every term is
  -- 1/(n*p) = 1/n * (1/p) (`one_div_mul_one_div_rev`, `mul_comm`); finish with `abel`
  have hs : (1 / ((n : ℝ) * p)) = (1 / (n : ℝ)) * (1 / (p : ℝ)) := by rw [one_div_mul_one_div]
  simp only [Wdual, Ymat, W0, GBp, hs, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, smul_add]
  abel

end PCError

end
