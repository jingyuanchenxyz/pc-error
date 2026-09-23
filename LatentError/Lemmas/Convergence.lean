import LatentError.Lemmas.Frames

/-!
# Convergence of eigenpairs; limits of the systematic Grams (Lemma 2, Propositions 1–2)
-/

open scoped Matrix Topology MatrixOrder
open Filter

noncomputable section

namespace PCError

variable {k n : ℕ}

/-- Lemma 2 (i), proof. -/
theorem eigpair_convergence {m : ℕ} (hFact2 : Fact2_Weyl m)
    (A : ℕ → Matrix (Fin m) (Fin m) ℝ) (Ainf : Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ p, (A p).IsHermitian) (hAinf : Ainf.IsHermitian)
    (hlim : Tendsto A atTop (𝓝 Ainf))
    (j : Fin m) (hsimple : ∀ i, i ≠ j → sortedEig Ainf i ≠ sortedEig Ainf j)
    (v : EuclideanSpace ℝ (Fin m)) (hv : IsUnitEigvec Ainf v (sortedEig Ainf j)) :
    (∀ᶠ p in atTop, ∀ i, i ≠ j → sortedEig (A p) i ≠ sortedEig (A p) j) ∧
    Tendsto (fun p => sortedEig (A p) j) atTop (𝓝 (sortedEig Ainf j)) ∧
    ∀ vp : ℕ → EuclideanSpace ℝ (Fin m),
      (∀ᶠ p in atTop, IsUnitEigvec (A p) (vp p) (sortedEig (A p) j)) →
      Tendsto (fun p => |inner ℝ (vp p) v|) atTop (𝓝 1) := by
  classical
  have hev : ∀ i, Tendsto (fun p => sortedEig (A p) i) atTop (𝓝 (sortedEig Ainf i)) :=
    tendsto_sortedEig hFact2 hA hAinf hlim
  refine ⟨?_, hev j, ?_⟩
  · rw [Filter.eventually_all]
    intro i
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun p h => absurd hij h
    · filter_upwards [((hev i).sub (hev j)).eventually_ne
        (sub_ne_zero.2 (hsimple i hij))] with p hp
      exact fun _ => sub_ne_zero.1 hp
  intro vp hvp
  -- replace `vp` by a sequence of unit vectors that agrees with it eventually
  let w : ℕ → EuclideanSpace ℝ (Fin m) := fun p =>
    if IsUnitEigvec (A p) (vp p) (sortedEig (A p) j) then vp p else v
  have hw_eq : ∀ᶠ p in atTop, w p = vp p := hvp.mono fun p hp => by simp only [w, if_pos hp]
  have hw_unit : ∀ p, ‖w p‖ = 1 := fun p => by
    by_cases h : IsUnitEigvec (A p) (vp p) (sortedEig (A p) j)
    · simp only [w, if_pos h]; exact h.1
    · simp only [w, if_neg h]; exact hv.1
  suffices Tendsto (fun p => |inner ℝ (w p) v|) atTop (𝓝 1) from
    this.congr' (hw_eq.mono fun p hp => by rw [hp])
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨wb, hwbmem, φ, hφ, hlimφ⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin m)) 1).tendsto_subseq
      (x := fun n => w (ns n)) (fun n => by simpa using hw_unit (ns n))
  refine ⟨φ, ?_⟩
  have hwb_unit : ‖wb‖ = 1 := by simpa using hwbmem
  have hsub : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hlimw : Tendsto (fun n => w (ns (φ n))) atTop (𝓝 wb) := hlimφ
  have heig : Matrix.toEuclideanLin Ainf wb = sortedEig Ainf j • wb := by
    have h1 : Tendsto (fun n => Matrix.toEuclideanLin Ainf (w (ns (φ n)))) atTop
        (𝓝 (Matrix.toEuclideanLin Ainf wb)) :=
      ((Matrix.toEuclideanLin Ainf).continuous_of_finiteDimensional.tendsto _).comp hlimw
    have h2 : Tendsto (fun n => sortedEig (A (ns (φ n))) j • w (ns (φ n))) atTop
        (𝓝 (sortedEig Ainf j • wb)) := ((hev j).comp hsub).smul hlimw
    have h3 : Tendsto (fun n => Matrix.toEuclideanLin Ainf (w (ns (φ n))) -
        sortedEig (A (ns (φ n))) j • w (ns (φ n))) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ ((tendsto_opNorm_sub hlim).comp hsub)
      filter_upwards [hsub.eventually hvp] with n hn
      have hwn : w (ns (φ n)) = vp (ns (φ n)) := by simp only [w, if_pos hn]
      rw [hwn, ← hn.2, ← toEuclideanLin_sub_apply]
      calc ‖Matrix.toEuclideanLin (Ainf - A (ns (φ n))) (vp (ns (φ n)))‖
          ≤ opNorm (Ainf - A (ns (φ n))) * ‖vp (ns (φ n))‖ := norm_toEuclideanLin_le _ _
        _ = opNorm (A (ns (φ n)) - Ainf) := by
          rw [hn.1, mul_one, ← neg_sub, opNorm, opNorm, map_neg, norm_neg]
    exact sub_eq_zero.1 (tendsto_nhds_unique (h1.sub h2) h3)
  have hlimabs : Tendsto (fun n => |inner ℝ (w (ns (φ n))) v|) atTop
      (𝓝 |inner ℝ wb v|) := (hlimw.inner tendsto_const_nhds).abs
  rcases unitEigvec_eq_or_eq_neg hAinf hsimple hv ⟨hwb_unit, heig⟩ with h | h
  · rwa [h, real_inner_self_eq_norm_sq, hv.1, one_pow, abs_one] at hlimabs
  · rwa [h, inner_neg_left, real_inner_self_eq_norm_sq, hv.1, one_pow, abs_neg,
      abs_one] at hlimabs

/-- Lemma 2 (ii), proof. -/
theorem sign_pinning {m : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin m))
    (u0 : EuclideanSpace ℝ (Fin m)) (hu : ∀ p, ‖u p‖ = 1) (hu0 : ‖u0‖ = 1)
    (hlim : Tendsto (fun p => |inner ℝ (u p) u0|) atTop (𝓝 1)) :
    (∀ᶠ p in atTop, inner ℝ (u p) u0 ≠ 0) ∧
    Tendsto (fun p => Real.sign (inner ℝ (u p) u0) • u p) atTop (𝓝 u0) := by
  have hne : ∀ᶠ p in atTop, inner ℝ (u p) u0 ≠ 0 := by
    filter_upwards [hlim.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with p hp
    exact abs_pos.1 hp
  refine ⟨hne, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ᶠ p in atTop, ‖Real.sign (inner ℝ (u p) u0) • u p - u0‖ =
      Real.sqrt (2 - 2 * |inner ℝ (u p) u0|) := by
    filter_upwards [hne] with p hp
    rw [← Real.sqrt_sq (norm_nonneg _), @norm_sub_sq_real, norm_smul, real_inner_smul_left,
      hu p, hu0]
    congr 1
    rcases lt_or_gt_of_ne hp with h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; norm_num; ring
    · rw [Real.sign_of_pos h, abs_of_pos h]; norm_num; ring
  have hlim2 : Tendsto (fun p => Real.sqrt (2 - 2 * |inner ℝ (u p) u0|)) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (2 : ℝ))).sub (hlim.const_mul 2)).sqrt
    simpa using this
  exact hlim2.congr' (key.mono fun p hp => hp.symm)

/-! ## Generic convergence tools -/

lemma tendsto_matrix_mul {ι : Type*} {L : Filter ι} {a b c : ℕ}
    {M : ι → Matrix (Fin a) (Fin b) ℝ} {N : ι → Matrix (Fin b) (Fin c) ℝ}
    {M0 : Matrix (Fin a) (Fin b) ℝ} {N0 : Matrix (Fin b) (Fin c) ℝ}
    (hM : Tendsto M L (𝓝 M0)) (hN : Tendsto N L (𝓝 N0)) :
    Tendsto (fun i => M i * N i) L (𝓝 (M0 * N0)) :=
  ((continuous_fst.matrix_mul continuous_snd).tendsto (M0, N0)).comp (hM.prodMk_nhds hN)

lemma tendsto_matrix_transpose {ι : Type*} {L : Filter ι} {a b : ℕ}
    {M : ι → Matrix (Fin a) (Fin b) ℝ} {M0 : Matrix (Fin a) (Fin b) ℝ}
    (hM : Tendsto M L (𝓝 M0)) : Tendsto (fun i => (M i)ᵀ) L (𝓝 M0ᵀ) :=
  (continuous_id.matrix_transpose.tendsto M0).comp hM

lemma tendsto_matrix_diagonal {ι : Type*} {L : Filter ι} {a : ℕ}
    {d : ι → Fin a → ℝ} {d0 : Fin a → ℝ} (hd : ∀ j, Tendsto (fun i => d i j) L (𝓝 (d0 j))) :
    Tendsto (fun i => Matrix.diagonal (d i)) L (𝓝 (Matrix.diagonal d0)) :=
  (continuous_id.matrix_diagonal.tendsto d0).comp (tendsto_pi_nhds.2 hd)

/-- Unit vectors whose inner product with a unit vector tends to `1` converge to it. -/
lemma tendsto_of_inner_tendsto_one {m : ℕ} {u : ℕ → EuclideanSpace ℝ (Fin m)}
    {u0 : EuclideanSpace ℝ (Fin m)} (hu : ∀ᶠ p in atTop, ‖u p‖ = 1) (hu0 : ‖u0‖ = 1)
    (h : Tendsto (fun p => inner ℝ (u p) u0) atTop (𝓝 1)) : Tendsto u atTop (𝓝 u0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ᶠ p in atTop, ‖u p - u0‖ = Real.sqrt (2 - 2 * inner ℝ (u p) u0) := by
    filter_upwards [hu] with p hp
    rw [← Real.sqrt_sq (norm_nonneg _), @norm_sub_sq_real, hp, hu0]
    congr 1; ring
  have hlim : Tendsto (fun p => Real.sqrt (2 - 2 * inner ℝ (u p) u0)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (2 : ℝ))).sub (h.const_mul 2)).sqrt
  exact hlim.congr' (key.mono fun p hp => hp.symm)

lemma sum_mul_eq_inner_colVec {a b : ℕ} (M N : Matrix (Fin a) (Fin b) ℝ) (j : Fin b) :
    ∑ i, M i j * N i j = inner ℝ (colVec M j) (colVec N j) := by
  simp [colVec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- Column-wise convergence gives matrix convergence. -/
lemma tendsto_of_tendsto_colVec {a b : ℕ} {M : ℕ → Matrix (Fin a) (Fin b) ℝ}
    {M0 : Matrix (Fin a) (Fin b) ℝ}
    (h : ∀ j, Tendsto (fun p => colVec (M p) j) atTop (𝓝 (colVec M0 j))) :
    Tendsto M atTop (𝓝 M0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have := ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin a) →L[ℝ] ℝ).continuous.tendsto _).comp
    (h j)
  simpa [colVec] using this

/-! ## `K⁽ᵖ⁾ → K` and eventual simplicity -/

lemma tendsto_kmat {G : ℕ → Matrix (Fin k) (Fin k) ℝ} {G0 : Matrix (Fin k) (Fin k) ℝ}
    (Sf : Matrix (Fin k) (Fin k) ℝ) (h : Tendsto G atTop (𝓝 G0)) :
    Tendsto (fun p => Kmat Sf (G p)) atTop (𝓝 (Kmat Sf G0)) :=
  (tendsto_const_nhds.mul h).mul tendsto_const_nhds

lemma kmat_limit_isHermitian (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) :
    (Kmat Sf P.GB).IsHermitian :=
  kmat_isHermitian (transpose_eq_of_isHermitian P.GB_posDef.isHermitian)

lemma tendsto_sortedEig_kp (hFact2k : Fact2_Weyl k) (P : LoadingParams k n)
    (Sf : Matrix (Fin k) (Fin k) ℝ) (i : Fin k) :
    Tendsto (fun p => sortedEig (Kmat Sf (GBp P.Barr p)) i) atTop
      (𝓝 (sortedEig (Kmat Sf P.GB) i)) :=
  tendsto_sortedEig hFact2k (fun p => kmat_isHermitian (gBp_transpose P.Barr p))
    (kmat_limit_isHermitian P Sf) (tendsto_kmat Sf P.A4) i

lemma eventually_kp_simple (hFact2k : Fact2_Weyl k) (P : LoadingParams k n)
    {Sf : Matrix (Fin k) (Fin k) ℝ} (hA5 : Assumption5 Sf P.GB) :
    ∀ᶠ p in atTop, StrictAnti (sortedEig (Kmat Sf (GBp P.Barr p))) ∧
      ∀ j, 0 < sortedEig (Kmat Sf (GBp P.Barr p)) j := by
  have hev := tendsto_sortedEig_kp hFact2k P Sf
  have h1 : ∀ᶠ p in atTop, ∀ i j : Fin k, i < j →
      sortedEig (Kmat Sf (GBp P.Barr p)) j < sortedEig (Kmat Sf (GBp P.Barr p)) i := by
    simp only [Filter.eventually_all]
    intro i j hij
    filter_upwards [((hev i).sub (hev j)).eventually
      (lt_mem_nhds (sub_pos.2 (hA5.1 hij)))] with p hp
    exact sub_pos.1 hp
  have h2 : ∀ᶠ p in atTop, ∀ j, 0 < sortedEig (Kmat Sf (GBp P.Barr p)) j := by
    rw [Filter.eventually_all]
    exact fun j => (hev j).eventually (lt_mem_nhds (hA5.2 j))
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨fun i j hij => hp1 i j hij, hp2⟩

lemma eventually_pmu_pos (hFact2k : Fact2_Weyl k) (P : LoadingParams k n)
    {Sf : Matrix (Fin k) (Fin k) ℝ} (hA5 : Assumption5 Sf P.GB) :
    ∀ᶠ p in atTop, p ≠ 0 ∧ ∀ j, 0 < pmu P.Barr Sf p j := by
  filter_upwards [eventually_kp_simple hFact2k P hA5, eventually_ne_atTop 0] with p hp hp0
  exact ⟨hp0, fun j => mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hp0)) (hp.2 j)⟩

/-! ## Sign changes of frames -/

lemma isPrincipalFrame_mul_signs {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    {b : Matrix (Fin p) (Fin k) ℝ} (hb : IsPrincipalFrame S b) {s : Fin k → ℝ}
    (hs : ∀ j, s j * s j = 1) : IsPrincipalFrame S (b * Matrix.diagonal s) := by
  refine isPrincipalFrame_of_mul_eq ?_ ?_
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc bᵀ, hb.1, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1; funext j; exact hs j
  · rw [← Matrix.mul_assoc, hb.mul_eq, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2; funext j; ring

lemma vpn_mul_diag (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ)
    (b : Matrix (Fin p) (Fin k) ℝ) (s : Fin k → ℝ) :
    Vpn Barr Sf p (b * Matrix.diagonal s) = Vpn Barr Sf p b * Matrix.diagonal s := by
  simp only [Vpn, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, mul_comm]

/-- Principal frames obeying the sign convention of Proposition 2 exist. -/
lemma exists_conv_frames (hFact2k : Fact2_Weyl k) (P : LoadingParams k n)
    {Sf : Matrix (Fin k) (Fin k) ℝ} (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB)
    (V : Matrix (Fin k) (Fin k) ℝ) :
    ∃ b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ,
      (∀ᶠ p in atTop, IsPrincipalFrame (Sig0 P.Barr Sf p) (b p)) ∧
      ∀ᶠ p in atTop, ∀ j, 0 ≤ ∑ i, Vpn P.Barr Sf p (b p) i j * V i j := by
  classical
  let b0 : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ := fun p =>
    if h : ∃ b : Matrix (Fin p) (Fin k) ℝ, IsPrincipalFrame (Sig0 P.Barr Sf p) b
    then h.choose else 0
  let s : (p : ℕ) → Fin k → ℝ := fun p j =>
    if 0 ≤ ∑ i, Vpn P.Barr Sf p (b0 p) i j * V i j then 1 else -1
  refine ⟨fun p => b0 p * Matrix.diagonal (s p), ?_, ?_⟩
  · filter_upwards [eventually_pmu_pos hFact2k P hA5] with p ⟨hp, hpos⟩
    have hex := exists_frame (Barr := P.Barr) hSf hp hpos
    have hb0 : IsPrincipalFrame (Sig0 P.Barr Sf p) (b0 p) := by
      simp only [b0, dif_pos hex]; exact hex.choose_spec
    exact isPrincipalFrame_mul_signs hb0 fun j => by
      simp only [s]; split_ifs <;> norm_num
  · refine Filter.Eventually.of_forall fun p j => ?_
    simp only [vpn_mul_diag, Matrix.mul_diagonal]
    have : ∑ i, Vpn P.Barr Sf p (b0 p) i j * s p j * V i j =
        s p j * ∑ i, Vpn P.Barr Sf p (b0 p) i j * V i j := by
      rw [Finset.mul_sum]; congr 1; funext i; ring
    rw [this]
    simp only [s]
    split_ifs with h
    · linarith
    · push_neg at h; linarith

/-- Under the sign convention, `V⁽ᵖ⁾ → V`. -/
lemma tendsto_vpn (hFact2k : Fact2_Weyl k) (P : LoadingParams k n)
    {Sf : Matrix (Fin k) (Fin k) ℝ} (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB)
    {V : Matrix (Fin k) (Fin k) ℝ} (hV : IsEigenbasis (Kmat Sf P.GB) V)
    {b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ}
    (hb : ∀ᶠ p in atTop, IsPrincipalFrame (Sig0 P.Barr Sf p) (b p))
    (hsign : ∀ᶠ p in atTop, ∀ j, 0 ≤ ∑ i, Vpn P.Barr Sf p (b p) i j * V i j) :
    Tendsto (fun p => Vpn P.Barr Sf p (b p)) atTop (𝓝 V) := by
  refine tendsto_of_tendsto_colVec fun j => ?_
  have hsimple : ∀ i, i ≠ j → sortedEig (Kmat Sf P.GB) i ≠ sortedEig (Kmat Sf P.GB) j :=
    fun i hij => hA5.1.injective.ne hij
  have heig : ∀ᶠ p in atTop, IsUnitEigvec (Kmat Sf (GBp P.Barr p))
      (colVec (Vpn P.Barr Sf p (b p)) j) (sortedEig (Kmat Sf (GBp P.Barr p)) j) := by
    filter_upwards [hb, eventually_pmu_pos hFact2k P hA5] with p hbp ⟨hp, hpos⟩
    exact (frame_facts hSf hp hpos hbp).2.2.2.2.isUnitEigvec j
  obtain ⟨-, -, hconv⟩ := eigpair_convergence hFact2k (fun p => Kmat Sf (GBp P.Barr p))
    (Kmat Sf P.GB) (fun p => kmat_isHermitian (gBp_transpose P.Barr p))
    (kmat_limit_isHermitian P Sf) (tendsto_kmat Sf P.A4) j hsimple (colVec V j)
    (hV.isUnitEigvec j)
  have habs := hconv _ heig
  refine tendsto_of_inner_tendsto_one (heig.mono fun p hp => hp.1) (hV.isUnitEigvec j).1 ?_
  refine habs.congr' (hsign.mono fun p hp => ?_)
  dsimp only
  rw [← sum_mul_eq_inner_colVec, abs_of_nonneg (hp j)]

/-! ## The systematic coordinates `Φ = bᵀ B F` -/

lemma sqrt_inv_mul {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) :
    (CFC.sqrt S)⁻¹ * CFC.sqrt S = 1 := by
  have hu : IsUnit (CFC.sqrt S) := (CFC.isUnit_sqrt_iff S (nonneg_of_posDef hS)).2 hS.isUnit
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)

lemma sqrt_mul_inv {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) :
    CFC.sqrt S * (CFC.sqrt S)⁻¹ = 1 :=
  mul_eq_one_comm.1 (sqrt_inv_mul hS)

section frame

variable {Barr : ℕ → Fin k → ℝ} {Sf : Matrix (Fin k) (Fin k) ℝ} {p : ℕ}
  {b : Matrix (Fin p) (Fin k) ℝ}

/-- `bᵀ B = Δ₀^{1/2} V⁽ᵖ⁾ᵀ Σ_f^{-1/2}`. -/
lemma frame_btB (hSf : Sf.PosDef) (hp : p ≠ 0) (hpos : ∀ j, 0 < pmu Barr Sf p j)
    (hb : IsPrincipalFrame (Sig0 Barr Sf p) b) :
    bᵀ * Bmat Barr p = Delta0Sqrt Barr Sf p * (Vpn Barr Sf p b)ᵀ * (CFC.sqrt Sf)⁻¹ := by
  have e4 := (frame_facts hSf hp hpos hb).2.2.2.1
  have h := congrArg Matrix.transpose e4
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, sqrt_transpose,
    delta0Sqrt_eq, Matrix.diagonal_transpose] at h
  rw [delta0Sqrt_eq, ← h]
  simp only [Matrix.mul_assoc, sqrt_mul_inv hSf, Matrix.mul_one]

/-- `Π B = B` for a principal frame. -/
lemma frame_proj_B (hSf : Sf.PosDef) (hp : p ≠ 0) (hpos : ∀ j, 0 < pmu Barr Sf p j)
    (hb : IsPrincipalFrame (Sig0 Barr Sf p) b) : b * bᵀ * Bmat Barr p = Bmat Barr p := by
  obtain ⟨e1, e2, -, -, -⟩ := frame_facts hSf hp hpos hb
  have hVVt : Vpn Barr Sf p b * (Vpn Barr Sf p b)ᵀ = 1 := mul_eq_one_comm.1 e1
  have hB : Bmat Barr p = b * (Delta0Sqrt Barr Sf p * (Vpn Barr Sf p b)ᵀ * (CFC.sqrt Sf)⁻¹) := by
    calc Bmat Barr p = Afac Barr Sf p * Vpn Barr Sf p b * (Vpn Barr Sf p b)ᵀ *
          (CFC.sqrt Sf)⁻¹ := by
          rw [Matrix.mul_assoc (Afac Barr Sf p), hVVt, Matrix.mul_one, Afac, Matrix.mul_assoc,
            sqrt_mul_inv hSf, Matrix.mul_one]
      _ = _ := by rw [e2]; simp only [Matrix.mul_assoc]
  rw [Matrix.mul_assoc, frame_btB hSf hp hpos hb]
  exact hB.symm

/-- `Φ̄ = Φ/√p = diag(√μ⁽ᵖ⁾) V⁽ᵖ⁾ᵀ Σ_f^{-1/2} F`. -/
lemma phibar_eq (hSf : Sf.PosDef) (hp : p ≠ 0) (hpos : ∀ j, 0 < pmu Barr Sf p j)
    (hb : IsPrincipalFrame (Sig0 Barr Sf p) b) (F : Matrix (Fin k) (Fin n) ℝ) :
    (1 / Real.sqrt p) • PhiMat b (Bmat Barr p) F =
      Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf (GBp Barr p)) j)) *
        (Vpn Barr Sf p b)ᵀ * (CFC.sqrt Sf)⁻¹ * F := by
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hp))
  have hd : (1 / Real.sqrt p) • Delta0Sqrt Barr Sf p =
      Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf (GBp Barr p)) j)) := by
    rw [delta0Sqrt_eq, ← Matrix.diagonal_smul]
    congr 1; funext j
    simp only [Pi.smul_apply, smul_eq_mul, pmu]
    rw [Real.sqrt_mul (Nat.cast_nonneg p)]
    field_simp
  rw [PhiMat, frame_btB hSf hp hpos hb, ← hd]
  simp only [Matrix.smul_mul]

/-- `ΦᵀΦ/(np) = Fᵀ G_B⁽ᵖ⁾ F/n` (eq. (52)). -/
lemma phi_gram (hSf : Sf.PosDef) (hp : p ≠ 0) (hpos : ∀ j, 0 < pmu Barr Sf p j)
    (hb : IsPrincipalFrame (Sig0 Barr Sf p) b) (F : Matrix (Fin k) (Fin n) ℝ) :
    (1 / ((n : ℝ) * p)) • ((PhiMat b (Bmat Barr p) F)ᵀ * PhiMat b (Bmat Barr p) F) =
      (1 / (n : ℝ)) • (Fᵀ * GBp Barr p * F) := by
  have hPB := frame_proj_B hSf hp hpos hb
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp
  have h : (PhiMat b (Bmat Barr p) F)ᵀ * PhiMat b (Bmat Barr p) F =
      Fᵀ * ((Bmat Barr p)ᵀ * (b * bᵀ * Bmat Barr p)) * F := by
    simp only [PhiMat, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h, hPB, GBp, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  by_cases hn : (n : ℝ) = 0
  · simp [hn]
  · field_simp

lemma npn_eq (hp : p ≠ 0) (B : Matrix (Fin p) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    Npn b B F = (1 / (n : ℝ)) • (((1 / Real.sqrt p) • PhiMat b B F) *
      ((1 / Real.sqrt p) • PhiMat b B F)ᵀ) := by
  have hsp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  have hsp0 : Real.sqrt p ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hp))).ne'
  simp only [Npn, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  by_cases hn : (n : ℝ) = 0
  · simp [hn]
  · field_simp
    rw [hsq]

end frame

section limits

variable (hFact2k : Fact2_Weyl k) (P : LoadingParams k n) {Sf : Matrix (Fin k) (Fin k) ℝ}
  (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ)
  {V : Matrix (Fin k) (Fin k) ℝ} (hV : IsEigenbasis (Kmat Sf P.GB) V)
  {b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ}
  (hb : ∀ᶠ p in atTop, IsPrincipalFrame (Sig0 P.Barr Sf p) (b p))
  (hsign : ∀ᶠ p in atTop, ∀ j, 0 ≤ ∑ i, Vpn P.Barr Sf p (b p) i j * V i j)
include hFact2k hSf hA5 hV hb hsign

lemma tendsto_phibar :
    Tendsto (fun p : ℕ => (1 / Real.sqrt p) • PhiMat (b p) (Bmat P.Barr p) F) atTop
      (𝓝 (PhiBarInf Sf P.GB V F)) := by
  have hlim : Tendsto (fun p : ℕ =>
      Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf (GBp P.Barr p)) j)) *
        (Vpn P.Barr Sf p (b p))ᵀ * (CFC.sqrt Sf)⁻¹ * F) atTop (𝓝 (PhiBarInf Sf P.GB V F)) := by
    unfold PhiBarInf
    refine tendsto_matrix_mul (tendsto_matrix_mul (tendsto_matrix_mul ?_
      (tendsto_matrix_transpose (tendsto_vpn hFact2k P hSf hA5 hV hb hsign)))
      tendsto_const_nhds) tendsto_const_nhds
    exact tendsto_matrix_diagonal fun j => (tendsto_sortedEig_kp hFact2k P Sf j).sqrt
  refine hlim.congr' ?_
  filter_upwards [hb, eventually_pmu_pos hFact2k P hA5] with p hbp ⟨hp, hpos⟩
  exact (phibar_eq hSf hp hpos hbp F).symm

lemma tendsto_npn :
    Tendsto (fun p : ℕ => Npn (b p) (Bmat P.Barr p) F) atTop (𝓝 (Nlim Sf P.GB V F)) := by
  have hΦ := tendsto_phibar hFact2k P hSf hA5 F hV hb hsign
  have hlim := (tendsto_matrix_mul hΦ (tendsto_matrix_transpose hΦ)).const_smul (1 / (n : ℝ))
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with p hp
  exact (npn_eq hp _ F).symm

end limits

lemma tendsto_w0p (P : LoadingParams k n) (F : Matrix (Fin k) (Fin n) ℝ) :
    Tendsto (fun p : ℕ => (1 / (n : ℝ)) • (Fᵀ * GBp P.Barr p * F)) atTop (𝓝 (W0 P.GB F)) :=
  (tendsto_matrix_mul (tendsto_matrix_mul tendsto_const_nhds P.A4) tendsto_const_nhds).const_smul _


end PCError

end
