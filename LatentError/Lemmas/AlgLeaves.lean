import LatentError.Lemmas.Prop3Leaves

/-!
# Leaf lemmas, batch 2

Small goals for the local harness (`harness/prove.py --all`); hints are in comments.
* Lemma 3 (change of basis): full rank gives an invertible Gram matrix, factorizations
  through the column space, and `bᵀ Σ₀ b = Δ₀` for a principal frame.
* Proposition 3: symmetry and spectrum of `W₀`, `W`, `W⁽ᵖ⁾`; the deterministic assembly
  `W⁽ᵖ⁾ → W` from the limits of the four terms.
* Remark after Corollary 3: entries of `F Fᵀ` and a moment bound.
-/

open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder

noncomputable section

namespace PCError

variable {k n : ℕ}

/-! ## Lemma 3 -/

lemma isUnit_transpose_mul_of_rank {p : ℕ} {B : Matrix (Fin p) (Fin k) ℝ} (hB : B.rank = k) :
    IsUnit (Bᵀ * B) := by
  -- hint: have h1 : (Bᵀ * B).rank = k := by rw [Matrix.rank_transpose_mul_self]; exact hB
  -- have h2 : LinearMap.range (Bᵀ * B).mulVecLin = ⊤ :=
  --   Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h1)
  -- exact Matrix.mulVec_surjective_iff_isUnit.1 (LinearMap.range_eq_top.1 h2)
  have h1 : (Bᵀ * B).rank = k := by rw [Matrix.rank_transpose_mul_self]; exact hB
  have h2 : LinearMap.range (Bᵀ * B).mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h1)
  exact Matrix.mulVec_surjective_iff_isUnit.1 (LinearMap.range_eq_top.1 h2)

lemma exists_mul_eq_of_range_le {p : ℕ} {B b : Matrix (Fin p) (Fin k) ℝ}
    (h : LinearMap.range b.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    ∃ M : Matrix (Fin k) (Fin k) ℝ, b = B * M := by
  -- hint: have hj : ∀ j : Fin k, ∃ x : Fin k → ℝ, B.mulVec x = b.mulVec (Pi.single j 1) :=
  --   fun j => h ⟨Pi.single j 1, rfl⟩
  -- choose x hx using hj; refine ⟨Matrix.of fun i j => x j i, ?_⟩; ext i j
  -- have := congrFun (hx j) i
  -- simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply] at this ⊢; linarith
  have hj : ∀ j : Fin k, ∃ x : Fin k → ℝ, B.mulVec x = b.mulVec (Pi.single j 1) :=
    fun j => h ⟨Pi.single j 1, rfl⟩
  choose x hx using hj
  refine ⟨Matrix.of fun i j => x j i, ?_⟩
  ext i j
  have := congrFun (hx j) i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply] at this ⊢
  linarith

lemma mul_inv_gram_mul {p : ℕ} {B b : Matrix (Fin p) (Fin k) ℝ} {M : Matrix (Fin k) (Fin k) ℝ}
    (hU : IsUnit (Bᵀ * B)) (hM : b = B * M) :
    B * ((Bᵀ * B)⁻¹ * Bᵀ * b) = b := by
  -- hint: have hd := (Matrix.isUnit_iff_isUnit_det _).1 hU; subst hM
  -- rw [Matrix.mul_assoc (Bᵀ * B)⁻¹ Bᵀ, ← Matrix.mul_assoc Bᵀ B M,
  --   ← Matrix.mul_assoc (Bᵀ * B)⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hU
  subst hM
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Bᵀ B M, ← Matrix.mul_assoc (Bᵀ * B)⁻¹ (Bᵀ * B) M,
    Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

lemma eq_of_mul_eq_gram {p : ℕ} {B b : Matrix (Fin p) (Fin k) ℝ} {C' : Matrix (Fin k) (Fin k) ℝ}
    (hU : IsUnit (Bᵀ * B)) (h : B * C' = b) :
    C' = (Bᵀ * B)⁻¹ * Bᵀ * b := by
  -- hint: have hd := (Matrix.isUnit_iff_isUnit_det _).1 hU; subst h
  -- rw [Matrix.mul_assoc (Bᵀ * B)⁻¹ Bᵀ, ← Matrix.mul_assoc Bᵀ B C',
  --   ← Matrix.mul_assoc (Bᵀ * B)⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hU
  subst h
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Bᵀ B C', ← Matrix.mul_assoc (Bᵀ * B)⁻¹ (Bᵀ * B) C',
    Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

lemma transpose_mul_mul_eq_one {p : ℕ} {B b : Matrix (Fin p) (Fin k) ℝ}
    {C : Matrix (Fin k) (Fin k) ℝ} (hb : bᵀ * b = 1) (hC : B * C = b) : bᵀ * B * C = 1 := by
  -- hint: rw [Matrix.mul_assoc, hC, hb]
  rw [Matrix.mul_assoc, hC, hb]

lemma mul_transpose_mul_eq_one {p : ℕ} {B b : Matrix (Fin p) (Fin k) ℝ}
    {C : Matrix (Fin k) (Fin k) ℝ} (h : bᵀ * B * C = 1) : C * (bᵀ * B) = 1 := by
  -- hint: exact mul_eq_one_comm.1 h
  exact mul_eq_one_comm.1 h

lemma transpose_mul_frame {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ} {b : Matrix (Fin p) (Fin k) ℝ}
    (hb : IsPrincipalFrame S b) :
    bᵀ * S * b = Matrix.diagonal (fun j : Fin k => sortedEigN S j) := by
  -- hint: rw [Matrix.mul_assoc, hb.mul_eq, ← Matrix.mul_assoc, hb.1, Matrix.one_mul]
  have h1 : bᵀ * b = 1 := hb.1
  rw [Matrix.mul_assoc, IsPrincipalFrame.mul_eq hb, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-! ## Proposition 3: symmetry and spectra -/

lemma w0_transpose {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GBᵀ = GB)
    (F : Matrix (Fin k) (Fin n) ℝ) : (W0 GB F)ᵀ = W0 GB F := by
  -- hint: simp [W0, Matrix.transpose_mul, Matrix.mul_assoc, hGB]
  simp [W0, Matrix.transpose_mul, Matrix.mul_assoc, hGB]

lemma w0_isHermitian {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GBᵀ = GB)
    (F : Matrix (Fin k) (Fin n) ℝ) : (W0 GB F).IsHermitian := by
  -- hint: exact isHermitian_of_transpose_eq (w0_transpose hGB F)
  exact isHermitian_of_transpose_eq (w0_transpose hGB F)

lemma wlim_transpose {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GBᵀ = GB)
    (F : Matrix (Fin k) (Fin n) ℝ) (δ2 : ℝ) : (Wlim GB F δ2)ᵀ = Wlim GB F δ2 := by
  -- hint: simp [Wlim, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
  --   w0_transpose hGB F]
  simp [Wlim, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, w0_transpose hGB F]

lemma sortedEig_wlim {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GBᵀ = GB)
    (F : Matrix (Fin k) (Fin n) ℝ) (δ2 : ℝ) :
    sortedEig (Wlim GB F δ2) = fun i => sortedEig (W0 GB F) i + δ2 / n := by
  -- hint: exact sortedEig_add_smul_one (w0_isHermitian hGB F) _
  exact sortedEig_add_smul_one (w0_isHermitian hGB F) _

lemma wdual_transpose (Barr : ℕ → Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (Zarr : ℕ → Fin n → ℝ) (p : ℕ) : (Wdual Barr F Zarr p)ᵀ = Wdual Barr F Zarr p := by
  -- hint: simp [Wdual, Matrix.transpose_mul]
  simp [Wdual, Matrix.transpose_mul]

lemma trace_wlim (hn : 0 < n) (GB : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (δ2 : ℝ) : (Wlim GB F δ2).trace = (W0 GB F).trace + δ2 := by
  -- hint: have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  -- simp [Wlim, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]; field_simp
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [Wlim, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    div_mul_cancel₀ _ hn']

lemma trace_eq_sum_sortedEig {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) :
    A.trace = ∑ j, sortedEig A j := by
  -- hint: rw [hA.trace_eq_sum_eigenvalues]; simp only [sortedEig_of_isHermitian hA];
  -- `hA.eigenvalues i` is `hA.eigenvalues₀` at an equivalence applied to `i`
  -- (unfold Matrix.IsHermitian.eigenvalues); both sides are sums of `hA.eigenvalues₀`
  -- reindexed by an equivalence: `Equiv.sum_comp` / `Fintype.sum_equiv`; `RCLike.ofReal_real_eq_id`
  rw [hA.trace_eq_sum_eigenvalues]
  simp only [sortedEig_of_isHermitian hA, Matrix.IsHermitian.eigenvalues, RCLike.ofReal_real_eq_id,
    id]
  exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm _).trans
    (Equiv.sum_comp (finCongr (Fintype.card_fin m).symm) _).symm

/-! ## Proposition 3: the limit of `W⁽ᵖ⁾` from its four terms -/

lemma smul_transpose_mul_truncRows_apply {p c : ℕ} (b : Matrix (Fin p) (Fin k) ℝ)
    (A : ℕ → Fin c → ℝ) (j : Fin k) (l : Fin c) :
    ((1 / (p : ℝ)) • (bᵀ * truncRows A p)) j l = (∑ i : Fin p, b i j * A i l) / p := by
  -- hint: rw [Matrix.smul_apply, transpose_mul_truncRows_apply, smul_eq_mul]; ring
  rw [Matrix.smul_apply, transpose_mul_truncRows_apply, smul_eq_mul]
  ring

lemma tendsto_noise_gram {Zarr : ℕ → Fin n → ℝ} {δ2 : ℝ}
    (h1 : ∀ l, Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.range p, Zarr i l ^ 2)
      atTop (𝓝 δ2))
    (h2 : ∀ l m, l ≠ m → Tendsto (fun p : ℕ => (1 / (p : ℝ)) *
      ∑ i ∈ Finset.range p, Zarr i l * Zarr i m) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ =>
        (1 / (n : ℝ)) • ((1 / (p : ℝ)) • ((truncRows Zarr p)ᵀ * truncRows Zarr p)))
      atTop (𝓝 ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  -- hint: refine tendsto_matrix_of_entries fun l m => ?_
  -- simp only [Matrix.smul_apply, smul_eq_mul, truncRows_transpose_mul_apply, smul_one_apply_fin]
  -- split_ifs with hlm
  -- · subst hlm; have := (h1 l).const_mul (1 / (n : ℝ)); simp only [sq] at this
  --   convert this using 2; ring
  -- · have := (h2 l m hlm).const_mul (1 / (n : ℝ)); simpa using this
  refine tendsto_matrix_of_entries fun l m => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, truncRows_transpose_mul_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero]
  split_ifs with hlm
  · subst hlm
    have := (h1 l).const_mul (1 / (n : ℝ))
    simp only [sq] at this
    convert this using 2
    ring
  · have := (h2 l m hlm).const_mul (1 / (n : ℝ))
    rw [mul_zero] at this
    exact this

lemma tendsto_cross_terms {X : ℕ → Matrix (Fin k) (Fin n) ℝ} (F : Matrix (Fin k) (Fin n) ℝ)
    (hX : Tendsto X atTop (𝓝 0)) :
    Tendsto (fun p => (1 / (n : ℝ)) • (Fᵀ * X p)) atTop (𝓝 0) := by
  -- hint: have := (tendsto_matrix_mul (tendsto_const_nhds (x := Fᵀ)) hX).const_smul (1 / (n : ℝ))
  -- simpa using this
  have := (tendsto_matrix_mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Fᵀ) atTop (𝓝 Fᵀ)) hX).const_smul (1 / (n : ℝ))
  rw [Matrix.mul_zero, smul_zero] at this
  exact this

lemma tendsto_wdual_of_parts {Barr : ℕ → Fin k → ℝ} {F : Matrix (Fin k) (Fin n) ℝ}
    {Zarr : ℕ → Fin n → ℝ} {GB : Matrix (Fin k) (Fin k) ℝ} {δ2 : ℝ}
    (hW0 : Tendsto (fun p => W0 (GBp Barr p) F) atTop (𝓝 (W0 GB F)))
    (hX : Tendsto (fun p : ℕ => (1 / (p : ℝ)) • ((Bmat Barr p)ᵀ * truncRows Zarr p))
      atTop (𝓝 0))
    (hZ : Tendsto (fun p : ℕ =>
        (1 / (n : ℝ)) • ((1 / (p : ℝ)) • ((truncRows Zarr p)ᵀ * truncRows Zarr p)))
      atTop (𝓝 ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ)))) :
    Tendsto (fun p => Wdual Barr F Zarr p) atTop (𝓝 (Wlim GB F δ2)) := by
  -- hint: have hc := tendsto_cross_terms F hX
  -- have hct := tendsto_matrix_transpose hc
  -- have h4 := ((hW0.add hc).add hct).add hZ
  -- simp only [Matrix.transpose_zero, add_zero] at h4
  -- rw [show (fun p => Wdual Barr F Zarr p) = _ from funext (wdual_expand Barr F Zarr)]
  -- unfold Wlim; exact h4
  have hc := tendsto_cross_terms F hX
  have hct := tendsto_matrix_transpose hc
  have h4 := ((hW0.add hc).add hct).add hZ
  rw [Matrix.transpose_zero, add_zero, add_zero] at h4
  rw [show (fun p => Wdual Barr F Zarr p) = _ from funext (wdual_expand Barr F Zarr)]
  exact h4

/-! ## Remark after Corollary 3 -/

lemma fcols_mul_transpose_apply (f : ℕ → Fin k → ℝ) (n : ℕ) (a b : Fin k) :
    (Fcols f n * (Fcols f n)ᵀ) a b = ∑ l ∈ Finset.range n, f l a * f l b := by
  -- hint: simp only [Matrix.mul_apply, Matrix.transpose_apply, Fcols, Matrix.of_apply]
  -- exact Fin.sum_univ_eq_sum_range (fun l => f l a * f l b) n
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fcols, Matrix.of_apply]
  exact Fin.sum_univ_eq_sum_range (fun l => f l a * f l b) n

lemma sq_mul_le_sum_sq_sq (x : Fin k → ℝ) (a b : Fin k) :
    (x a * x b) ^ 2 ≤ (∑ c, x c ^ 2) ^ 2 := by
  -- hint: have ha : x a ^ 2 ≤ ∑ c, x c ^ 2 :=
  --   Finset.single_le_sum (f := fun c => x c ^ 2) (fun c _ => sq_nonneg _) (Finset.mem_univ a)
  -- have hb : (same with b)
  -- rw [mul_pow, sq (∑ c, x c ^ 2)]; exact mul_le_mul ha hb (sq_nonneg _) ((sq_nonneg _).trans ha)
  have ha : x a ^ 2 ≤ ∑ c, x c ^ 2 :=
    Finset.single_le_sum (f := fun c => x c ^ 2) (fun c _ => sq_nonneg _) (Finset.mem_univ a)
  have hb : x b ^ 2 ≤ ∑ c, x c ^ 2 :=
    Finset.single_le_sum (f := fun c => x c ^ 2) (fun c _ => sq_nonneg _) (Finset.mem_univ b)
  rw [mul_pow, sq (∑ c, x c ^ 2)]
  exact mul_le_mul ha hb (sq_nonneg _) ((sq_nonneg _).trans ha)

end PCError

end
