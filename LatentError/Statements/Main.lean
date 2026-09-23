import LatentError.Statements.Appendix
import LatentError.Bridge.Real
import LatentError.Lemmas.Thm3Leaves

/-!
# Statements of the main results (Sections 6–7)

Theorem 1 (error decomposition), Theorem 2 (observable floor), Corollary 1 (aggregate
out-of-subspace error) and Theorem 3 (rotation error is not estimable), numbered as in the
Sept 14, 2026 version of the paper.  The statements were frozen before any proof search
(`harness/freeze.py`); all of them are now proved.

As in the Ono/AxiomProver protocol, each headline theorem takes the three background
facts as explicit hypotheses, at dimensions `n` (the dual `W⁽ᵖ⁾`) and `k` (`K⁽ᵖ⁾`, `N`).

Quantifier structure of the asymptotic statements (Theorems 1–2, Corollary 1):
the population data (`P`, `Σ_f`, `F`, an eigenbasis `V` of `K` and unit eigenvectors `νⱼ`
of `N`) are fixed first.  Then *one* almost-sure event is asserted on which the
conclusions hold for **every** sequence of principal frames `b⁽ᵖ⁾` of `Σ₀` and **every**
choice of unit eigenvectors `hⱼ⁽ᵖ⁾` of `S⁽ᵖ⁾`, required only for large `p`.  All
conclusions are invariant under the sign choices.
-/

open scoped Matrix Topology MatrixOrder ProbabilityTheory
open Filter MeasureTheory ProbabilityTheory

noncomputable section

set_option linter.unusedVariables false

namespace PCError

variable {k n : ℕ}

/-! ## 6.1 Error decomposition -/

/-- **Eq. (16)/(24) (exact angular split, valid at every `p`).**  For `b` with orthonormal
columns and `Π h ≠ 0`:
`sin²∠(h, bⱼ) = sin²∠(h, col b) + cos²∠(h, col b) · sin²∠(Π h, bⱼ)`. -/
theorem exact_split {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (h : EuclideanSpace ℝ (Fin p)) (hproj : Matrix.toEuclideanLin (projB b) h ≠ 0)
    (j : Fin k) :
    sinSq h (colVec b j) =
      sinSqSub h b + (1 - sinSqSub h b) *
        sinSq (Matrix.toEuclideanLin (projB b) h) (colVec b j) := by
  have hh : h ≠ 0 := by rintro rfl; exact hproj (map_zero _)
  have hPh : ‖Matrix.toEuclideanLin (projB b) h‖ ≠ 0 := norm_ne_zero_iff.mpr hproj
  have hhn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  unfold sinSq sinSqSub
  rw [norm_colVec b hb j, inner_colVec_eq_inner_projB b hb h j]
  field_simp
  ring

/-- **Eq. (25).**  For a unit vector `h`, `sin²∠(h, col b) = ‖Π⊥ h‖²` and
`cos²∠(h, col b) = ‖Π h‖²`. -/
theorem eq25_projection_norms {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (h : EuclideanSpace ℝ (Fin p)) (hh : ‖h‖ = 1) :
    sinSqSub h b = ‖Matrix.toEuclideanLin (1 - projB b) h‖ ^ 2 ∧
    1 - sinSqSub h b = ‖Matrix.toEuclideanLin (projB b) h‖ ^ 2 := by
  have hsub : sinSqSub h b = 1 - ‖Matrix.toEuclideanLin (projB b) h‖ ^ 2 := by
    simp [sinSqSub, hh]
  refine ⟨?_, ?_⟩
  · rw [hsub, norm_one_sub_projB_sq b hb, hh]; ring
  · rw [hsub]; ring

/-! ### From Ono's theorems to Theorem 1

`ono_limits_path` applies Ono's proved `theorem1_error_decomposition` and
`corollary1_observable_floor` to the model built from the real data
(`LatentError/Bridge/Real.lean`), along one noise path and for the sign-normalized frames
`b★`.  Theorem 1 then follows for arbitrary principal frames, which differ from `b★` by
column signs (`frame_eq_mul_signs`). -/

lemma sig0_isHermitian (Barr : ℕ → Fin k → ℝ) {Sf : Matrix (Fin k) (Fin k) ℝ}
    (hSf : Sf.PosDef) (p : ℕ) : (Sig0 Barr Sf p).IsHermitian :=
  isHermitian_of_transpose_eq (by
    simp [Sig0, Matrix.transpose_mul, Matrix.mul_assoc,
      transpose_eq_of_isHermitian hSf.isHermitian])

/-- For large `p`, the top `k` eigenvalues of `Σ₀` are simple. -/
lemma sig0_simple {Barr : ℕ → Fin k → ℝ} {Sf : Matrix (Fin k) (Fin k) ℝ} (hSf : Sf.PosDef)
    {p : ℕ} (hp : p ≠ 0) (hkp : k ≤ p) (hpos : ∀ j, 0 < pmu Barr Sf p j)
    (hK : StrictAnti (sortedEig (Kmat Sf (GBp Barr p)))) (i : Fin k) (i' : Fin p)
    (hne : i' ≠ Fin.castLE hkp i) :
    sortedEig (Sig0 Barr Sf p) i' ≠ sortedEig (Sig0 Barr Sf p) (Fin.castLE hkp i) := by
  have hS : ∀ m : Fin p, sortedEig (Sig0 Barr Sf p) m =
      (p : ℝ) * sortedEigN (Kmat Sf (GBp Barr p)) m := fun m => by
    rw [← sortedEigN_sig0 Barr hSf hp, sortedEigN_eq_fin _ _ m.2]
  rw [hS, hS]
  have hi : sortedEigN (Kmat Sf (GBp Barr p)) (Fin.castLE hkp i) =
      sortedEig (Kmat Sf (GBp Barr p)) i := sortedEigN_eq_fin _ _ i.2
  rw [hi]
  by_cases hi' : (i' : ℕ) < k
  · rw [sortedEigN_eq_fin _ _ hi']
    intro heq
    have h1 := hK.injective (mul_left_cancel₀ (Nat.cast_ne_zero.2 hp) heq)
    exact hne (Fin.ext (by simpa using congrArg Fin.val h1))
  · rw [sortedEigN, dif_neg hi', mul_zero]
    intro heq
    exact (hpos i).ne' heq.symm

/-- Two principal frames with simple top eigenvalues differ by column signs. -/
lemma frame_eq_mul_signs {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.IsHermitian)
    (hkp : k ≤ p)
    (hsimple : ∀ (i : Fin k) (i' : Fin p), i' ≠ Fin.castLE hkp i →
      sortedEig S i' ≠ sortedEig S (Fin.castLE hkp i))
    {b b' : Matrix (Fin p) (Fin k) ℝ} (hb : IsPrincipalFrame S b)
    (hb' : IsPrincipalFrame S b') :
    ∃ s : Fin k → ℝ, (∀ i, s i * s i = 1) ∧ b' = b * Matrix.diagonal s := by
  have hcol : ∀ i : Fin k, colVec b' i = colVec b i ∨ colVec b' i = -colVec b i := by
    intro i
    have e : sortedEigN S i = sortedEig S (Fin.castLE hkp i) := sortedEigN_eq_fin _ _ _
    refine unitEigvec_eq_or_eq_neg hS (hsimple i) ⟨norm_colVec b hb.1 i, ?_⟩
      ⟨norm_colVec b' hb'.1 i, ?_⟩
    · rw [← e]; exact hb.2 i
    · rw [← e]; exact hb'.2 i
  refine ⟨fun i => if colVec b' i = colVec b i then 1 else -1,
    fun i => by dsimp only; split_ifs <;> norm_num, ?_⟩
  refine ext_colVec fun i => ?_
  rw [colVec_mul_diagonal]
  dsimp only
  split_ifs with h1
  · rw [h1, one_smul]
  · rcases hcol i with h2 | h2
    · exact absurd h2 h1
    · rw [h2, neg_one_smul]

/-- Ono's two limits along one noise path, for the sign-normalized frames `bs`. -/
lemma ono_limits_path (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n)
    (hFact3n : Fact3_EigCont n) (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k)
    (P : LoadingParams k n) {Sf : Matrix (Fin k) (Fin k) ℝ} (hSf : Sf.PosDef)
    (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F)
    {V : Matrix (Fin k) (Fin k) ℝ} (hV : IsEigenbasis (Kmat Sf P.GB) V)
    (ν : Fin k → EuclideanSpace ℝ (Fin k))
    (hν : ∀ j, IsUnitEigvec (Nlim Sf P.GB V F) (ν j) (sortedEig (Nlim Sf P.GB V F) j))
    (bs : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ)
    (hbs : ∀ᶠ p in atTop, IsPrincipalFrame (Sig0 P.Barr Sf p) (bs p))
    (hsign : ∀ᶠ p in atTop, ∀ j, 0 ≤ ∑ i, Vpn P.Barr Sf p (bs p) i j * V i j)
    (Zarr : ℕ → Fin n → ℝ)
    (hG : Tendsto (fun p : ℕ => (1 / (n : ℝ)) •
      ((1 / (p : ℝ)) • ((truncRows Zarr p)ᵀ * truncRows Zarr p))) atTop
      (𝓝 ((P.δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ))))
    (hX : Tendsto (fun p : ℕ => (1 / (p : ℝ)) • ((Bmat P.Barr p)ᵀ * truncRows Zarr p))
      atTop (𝓝 0))
    (hbZ : Tendsto (fun p : ℕ => (1 / Real.sqrt p) • ((bs p)ᵀ * truncRows Zarr p))
      atTop (𝓝 0))
    (h : (p : ℕ) → Fin k → EuclideanSpace ℝ (Fin p))
    (hh : ∀ᶠ p in atTop, ∀ j, IsUnitEigvec (Scov P.Barr F Zarr p) (h p j)
      (sortedEigN (Scov P.Barr F Zarr p) j))
    (j : Fin k) :
    Tendsto (fun p => sinSq (h p j) (colVec (bs p) j)) atTop
      (𝓝 (thm1Limit n P.δ2 (lam P.GB F j) (sinSq (ν j) (e j)))) ∧
    Tendsto (fun p => ‖Matrix.toEuclideanLin (1 - bs p * (bs p)ᵀ) (h p j)‖ ^ 2) atTop
      (𝓝 (P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2))) := by
  obtain ⟨M, hMbh, hMlam, hMν⟩ :=
    exists_model hFact2k hFact2n P hSf hA5 F hA6 hV bs hbs hsign Zarr hG hX hbZ h hh
  have T1 : Tendsto (fun Q : Adm k => sinSq (M.h Q j) (colVec (M.b Q) j)) atTop
      (𝓝 (P.δ2 / ((n : ℝ) * M.lam j + P.δ2) +
        ((n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + P.δ2)) * sinSq (M.νn j) (e j))) :=
    _root_.theorem1_error_decomposition M hFact1 hFact2n hFact3n hFact2k hFact3k j
  have C1 : Tendsto (fun Q : Adm k =>
      ‖Matrix.toEuclideanLin (1 - M.b Q * (M.b Q)ᵀ) (M.h Q j)‖ ^ 2) atTop
      (𝓝 (P.δ2 / ((n : ℝ) * M.lam j + P.δ2))) :=
    (_root_.corollary1_observable_floor M hFact1 hFact2n hFact3n hFact2k hFact3k j).2.2.1
  have hsin : sinSq (M.νn j) (e j) = sinSq (ν j) (e j) := by
    have hsimple : ∀ i, i ≠ j →
        sortedEig (Nlim Sf P.GB V F) i ≠ sortedEig (Nlim Sf P.GB V F) j := by
      intro i hij
      rw [sortedEig_nlim hSf hA5 hV, sortedEig_nlim hSf hA5 hV]
      exact hA6.1.injective.ne hij
    have h1 : IsUnitEigvec (Nlim Sf P.GB V F) (M.νn j) (sortedEig (Nlim Sf P.GB V F) j) := by
      rw [sortedEig_nlim hSf hA5 hV F j]
      exact hMν j
    exact sinSq_eq_of_eq_or_neg (unitEigvec_eq_or_eq_neg (nlim_isHermitian F) hsimple (hν j) h1) _
  rw [hMlam j, hsin] at T1
  rw [hMlam j] at C1
  refine ⟨(tendsto_adm_iff (k := k)).1 (T1.congr' ?_), (tendsto_adm_iff (k := k)).1 (C1.congr' ?_)⟩
  · filter_upwards [hMbh] with Q hQ
    rw [hQ.1, hQ.2]
  · filter_upwards [hMbh] with Q hQ
    rw [hQ.1, hQ.2]

/-- **Theorem 1 (Error decomposition).**  Under Assumptions 1–6, conditional on `F` and
almost surely as `p → ∞`, for each `j`:
(i)  `sin²∠(hⱼ, bⱼ) → δ²/(nλⱼ+δ²) + nλⱼ/(nλⱼ+δ²) · sin²∠(νⱼ, eⱼ)`   (eq. (17));
(ii) `Π hⱼ ≠ 0` for all large `p`, `sin²∠(hⱼ, B) → δ²/(nλⱼ+δ²)`,
     `cos²∠(hⱼ, B) → nλⱼ/(nλⱼ+δ²)` (eq. (18)), and
     `sin²∠(Π hⱼ, bⱼ) → sin²∠(νⱼ, eⱼ)` (eq. (19)).
Here `(λⱼ, νⱼ)` is the `j`-th eigenpair of the limiting systematic dual Gram `N`. -/
theorem theorem1_error_decomposition
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k)
    (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef)
    (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (N : NoiseModel n P.var P.κ4 Ω μ)
    (V : Matrix (Fin k) (Fin k) ℝ) (hV : IsEigenbasis (Kmat Sf P.GB) V)
    (ν : Fin k → EuclideanSpace ℝ (Fin k))
    (hν : ∀ j, IsUnitEigvec (Nlim Sf P.GB V F) (ν j) (sortedEig (Nlim Sf P.GB V F) j)) :
    ∀ᵐ ω ∂μ, ∀ (b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ)
      (h : (p : ℕ) → Fin k → EuclideanSpace ℝ (Fin p)),
      (∀ᶠ p in atTop, IsPrincipalFrame (Sig0 P.Barr Sf p) (b p)) →
      (∀ᶠ p in atTop, ∀ j, IsUnitEigvec (Scov P.Barr F (N.path ω) p) (h p j)
        (sortedEigN (Scov P.Barr F (N.path ω) p) j)) →
      ∀ j : Fin k,
        -- (i), eq. (17)
        Tendsto (fun p => sinSq (h p j) (colVec (b p) j)) atTop
          (𝓝 (thm1Limit n P.δ2 (lam P.GB F j) (sinSq (ν j) (e j)))) ∧
        -- (ii)
        (∀ᶠ p in atTop, Matrix.toEuclideanLin (projB (b p)) (h p j) ≠ 0) ∧
        Tendsto (fun p => sinSqSub (h p j) (b p)) atTop
          (𝓝 (P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2))) ∧
        Tendsto (fun p => ‖Matrix.toEuclideanLin (projB (b p)) (h p j)‖ ^ 2 / ‖h p j‖ ^ 2)
          atTop (𝓝 ((n : ℝ) * lam P.GB F j / ((n : ℝ) * lam P.GB F j + P.δ2))) ∧
        Tendsto (fun p => sinSq (Matrix.toEuclideanLin (projB (b p)) (h p j)) (colVec (b p) j))
          atTop (𝓝 (sinSq (ν j) (e j))) := by
  obtain ⟨bs, hbs, hsign⟩ := exists_conv_frames hFact2k P hSf hA5 V
  filter_upwards [N.gram_limit hFact1 P.A3, N.cross_limit P,
    N.frame_noise_limit bs (hbs.mono fun p hp => hp.1)] with ω hG hX hbZ
  intro b h hb hh j
  obtain ⟨L1, L2⟩ := ono_limits_path hFact1 hFact2n hFact3n hFact2k hFact3k P hSf hA5 F hA6
    hV ν hν bs hbs hsign (N.path ω) hG hX hbZ h hh j
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by have := P.hkn; omega)
  have hl : 0 < lam P.GB F j := hA6.2 j
  have hden : (n : ℝ) * lam P.GB F j + P.δ2 ≠ 0 := (add_pos (mul_pos hn hl) P.δ2_pos).ne'
  have hsgn : ∀ᶠ p in atTop, ∃ s : Fin k → ℝ, (∀ i, s i * s i = 1) ∧
      b p = bs p * Matrix.diagonal s := by
    filter_upwards [hbs, hb, eventually_ge_atTop k, eventually_pmu_pos hFact2k P hA5,
      eventually_kp_simple hFact2k P hA5] with p h1 h2 hkp hpp hK
    exact frame_eq_mul_signs (sig0_isHermitian P.Barr hSf p) hkp
      (sig0_simple hSf hpp.1 hkp hpp.2 hK.1) h1 h2
  have hunit : ∀ᶠ p in atTop, ‖h p j‖ = 1 := hh.mono fun p hp => (hp j).1
  have hbo : ∀ᶠ p in atTop, (b p)ᵀ * b p = 1 := hb.mono fun p hp => hp.1
  -- (i)
  have hi : Tendsto (fun p => sinSq (h p j) (colVec (b p) j)) atTop
      (𝓝 (thm1Limit n P.δ2 (lam P.GB F j) (sinSq (ν j) (e j)))) := by
    refine L1.congr' ?_
    filter_upwards [hsgn] with p hp
    obtain ⟨s, hs, hbp⟩ := hp
    rw [hbp, colVec_mul_signs]
    rcases mul_self_eq_one_iff.1 (hs j) with h1 | h1
    · rw [h1, one_smul]
    · rw [h1, neg_one_smul, sinSq_neg_right]
  -- (18), out-of-subspace part
  have hsub : Tendsto (fun p => sinSqSub (h p j) (b p)) atTop
      (𝓝 (P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2))) := by
    refine L2.congr' ?_
    filter_upwards [hsgn, hunit, hbo] with p hp hu ho
    obtain ⟨s, hs, hbp⟩ := hp
    rw [(eq25_projection_norms (b p) ho (h p j) hu).1, hbp, projB_mul_signs _ _ hs]
    rfl
  have hc_eq : (1 : ℝ) - P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2) =
      (n : ℝ) * lam P.GB F j / ((n : ℝ) * lam P.GB F j + P.δ2) := by
    field_simp
    ring
  -- (18), in-subspace part
  have hcos : Tendsto (fun p => ‖Matrix.toEuclideanLin (projB (b p)) (h p j)‖ ^ 2 / ‖h p j‖ ^ 2)
      atTop (𝓝 ((n : ℝ) * lam P.GB F j / ((n : ℝ) * lam P.GB F j + P.δ2))) := by
    have h1 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hsub
    rw [hc_eq] at h1
    refine h1.congr fun p => ?_
    unfold sinSqSub
    ring
  have hcpos : 0 < (n : ℝ) * lam P.GB F j / ((n : ℝ) * lam P.GB F j + P.δ2) :=
    div_pos (mul_pos hn hl) (add_pos (mul_pos hn hl) P.δ2_pos)
  have hne : ∀ᶠ p in atTop, Matrix.toEuclideanLin (projB (b p)) (h p j) ≠ 0 := by
    filter_upwards [hcos.eventually (lt_mem_nhds hcpos)] with p hp h0
    rw [h0, norm_zero] at hp
    simp at hp
  -- (19)
  have h19 : Tendsto (fun p => sinSq (Matrix.toEuclideanLin (projB (b p)) (h p j))
      (colVec (b p) j)) atTop (𝓝 (sinSq (ν j) (e j))) := by
    have hq := (hi.sub hsub).div
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hsub)
      (by rw [hc_eq]; exact hcpos.ne')
    rw [hc_eq, inSubspace_algebra n P.δ2 (lam P.GB F j) _ P.δ2_pos hl
      (by have := P.hkn; omega)] at hq
    refine hq.congr' ?_
    filter_upwards [hne, hbo, hunit] with p hp ho hu
    have hs := exact_split (b p) ho (h p j) hp j
    have hd : 1 - sinSqSub (h p j) (b p) ≠ 0 := by
      rw [(eq25_projection_norms (b p) ho (h p j) hu).2]
      exact (pow_pos (norm_pos_iff.2 hp) 2).ne'
    rw [Pi.div_apply, hs, add_sub_cancel_left, mul_div_cancel_left₀ _ hd]
  exact ⟨hi, hne, hsub, hcos, h19⟩

/-- **Eq. (20).**  With `SNRⱼ = nλⱼ/δ²`, the Theorem 1 limit is
`1/(1+SNRⱼ) + SNRⱼ/(1+SNRⱼ) · sin²∠(νⱼ, eⱼ)`. -/
theorem thm1Limit_snr (n : ℕ) (δ2 lamj s : ℝ) (hδ : 0 < δ2) (hl : 0 ≤ lamj) :
    thm1Limit n δ2 lamj s =
      1 / (1 + (n : ℝ) * lamj / δ2) +
        ((n : ℝ) * lamj / δ2) / (1 + (n : ℝ) * lamj / δ2) * s := by
  unfold thm1Limit
  field_simp [hδ, hl]
  ring

/-! ## 7.1 Out-of-subspace error is estimable from data -/

/-- **Theorem 2 (A data-driven estimate for out-of-subspace error).**  Under
Assumptions 1–6, conditional on `F` and almost surely as `p → ∞`:
`ℓ⁽ᵖ⁾ → δ²/n`, `θⱼ⁽ᵖ⁾ → λⱼ + δ²/n`, and
`lim ℓ⁽ᵖ⁾/θⱼ⁽ᵖ⁾ = δ²/(nλⱼ+δ²) = lim sin²∠(hⱼ, B)` (eq. (38)).  Hence
`lim ℓ⁽ᵖ⁾/θⱼ⁽ᵖ⁾ ≤ lim sin²∠(hⱼ, bⱼ)`, with equality iff `sin²∠(νⱼ, eⱼ) = 0` (eq. (39)). -/
theorem theorem2_observable_floor
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k)
    (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef)
    (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (N : NoiseModel n P.var P.κ4 Ω μ)
    (V : Matrix (Fin k) (Fin k) ℝ) (hV : IsEigenbasis (Kmat Sf P.GB) V)
    (ν : Fin k → EuclideanSpace ℝ (Fin k))
    (hν : ∀ j, IsUnitEigvec (Nlim Sf P.GB V F) (ν j) (sortedEig (Nlim Sf P.GB V F) j)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun p => ellBulk P.Barr F (N.path ω) p) atTop (𝓝 (P.δ2 / n)) ∧
      ∀ j : Fin k,
        Tendsto (fun p => theta P.Barr F (N.path ω) p j) atTop
          (𝓝 (lam P.GB F j + P.δ2 / n)) ∧
        -- eq. (38)
        Tendsto (fun p => ellBulk P.Barr F (N.path ω) p / theta P.Barr F (N.path ω) p j) atTop
          (𝓝 (P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2))) ∧
        (∀ (b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ)
          (h : (p : ℕ) → Fin k → EuclideanSpace ℝ (Fin p)),
          (∀ᶠ p in atTop, IsPrincipalFrame (Sig0 P.Barr Sf p) (b p)) →
          (∀ᶠ p in atTop, ∀ i, IsUnitEigvec (Scov P.Barr F (N.path ω) p) (h p i)
            (sortedEigN (Scov P.Barr F (N.path ω) p) i)) →
          Tendsto (fun p => sinSqSub (h p j) (b p)) atTop
            (𝓝 (P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2))) ∧
          Tendsto (fun p => sinSq (h p j) (colVec (b p) j)) atTop
            (𝓝 (thm1Limit n P.δ2 (lam P.GB F j) (sinSq (ν j) (e j))))) ∧
        -- eq. (39), comparing the two limits
        P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2) ≤
          thm1Limit n P.δ2 (lam P.GB F j) (sinSq (ν j) (e j)) ∧
        (P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2) =
            thm1Limit n P.δ2 (lam P.GB F j) (sinSq (ν j) (e j)) ↔
          sinSq (ν j) (e j) = 0) := by
  have hn' : 0 < n := by have := P.hkn; omega
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 hn'
  have hW : ∀ᵐ ω ∂μ, Tendsto (fun p => Wdual P.Barr F (N.path ω) p) atTop
      (𝓝 (Wlim P.GB F P.δ2)) := by
    filter_upwards [N.gram_limit hFact1 P.A3, N.cross_limit P] with ω h1 h2
    exact tendsto_wdual_of_parts (tendsto_w0p P F) h2 h1
  filter_upwards [hW, theorem1_error_decomposition hFact1 hFact2n hFact3n hFact2k hFact3k P Sf
    hSf hA5 F hA6 N V hV ν hν] with ω hω hT1
  have hθ := fun j : Fin k => theta_limit hFact2n P F hω j
  have hell : Tendsto (fun p => ellBulk P.Barr F (N.path ω) p) atTop (𝓝 (P.δ2 / n)) := by
    have hsum : Tendsto (fun p => ∑ i ∈ Finset.range k, theta P.Barr F (N.path ω) p i) atTop
        (𝓝 (∑ i ∈ Finset.range k, (lam P.GB F i + P.δ2 / n))) :=
      tendsto_finset_sum _ fun i hi => hθ ⟨i, Finset.mem_range.1 hi⟩
    have h1 := ((tendsto_trace hω).sub hsum).div_const ((n : ℝ) - k)
    rw [trace_wlim hn' P.GB F P.δ2, trace_w0_eq_sum_lam P.GB_posDef P.hkn.le F,
      ← sum_range_eq_sum_fin (lam P.GB F), bulk_limit_algebra P.hkn P.δ2 (lam P.GB F)] at h1
    exact h1
  refine ⟨hell, fun j => ?_⟩
  have hl : 0 < lam P.GB F j := hA6.2 j
  have hθpos : lam P.GB F j + P.δ2 / n ≠ 0 := (add_pos hl (div_pos P.δ2_pos hn)).ne'
  have hratio := hell.div (hθ j) hθpos
  rw [ratio_limit hn' P.δ2 (lam P.GB F j) P.δ2_pos hl.le] at hratio
  have hs0 : 0 ≤ sinSq (ν j) (e j) :=
    (sinSq_mem_Icc_of_unit (hν j).1 (by simp [e])).1
  refine ⟨hθ j, hratio, fun b h hb hh => ?_,
    floor_le_thm1Limit n P.δ2 (lam P.GB F j) _ P.δ2_pos hl.le hs0,
    floor_eq_thm1Limit_iff n hn' P.δ2 (lam P.GB F j) _ P.δ2_pos hl⟩
  obtain ⟨h1, -, h3, -, -⟩ := hT1 b h hb hh j
  exact ⟨h3, h1⟩

/-- **Corollary 1 (Aggregate out-of-subspace error).**
At every `p`, for `b` and `H = [h₁ ⋯ h_k]` with orthonormal columns,
`Σⱼ sin²∠(hⱼ, B) = ½‖Π_H − Π_B‖_F² = Σᵢ sin²ηᵢ` (eqs. (40)–(41)), where
`cos²ηᵢ` are the squared singular values of `bᵀH`, i.e. the eigenvalues of `(bᵀH)ᵀ(bᵀH)`.
Under Assumptions 1–6, conditional on `F` and almost surely, `½‖Π_H − Π_B‖_F² →
Σⱼ δ²/(nλⱼ+δ²) > 0`, and the observable statistic `Σⱼ ℓ/θⱼ` has the same limit. -/
theorem corollary1_aggregate
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k)
    (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef)
    (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (N : NoiseModel n P.var P.κ4 Ω μ) :
    (∀ (p : ℕ) (b : Matrix (Fin p) (Fin k) ℝ) (h : Fin k → EuclideanSpace ℝ (Fin p)),
      bᵀ * b = 1 → (Hmat h)ᵀ * Hmat h = 1 →
      ∑ j, sinSqSub (h j) b = (1 / 2 : ℝ) * frobSq (projH h - projB b) ∧
      ∑ i, (1 - sortedEig ((bᵀ * Hmat h)ᵀ * (bᵀ * Hmat h)) i) =
        (1 / 2 : ℝ) * frobSq (projH h - projB b)) ∧
    0 < ∑ j : Fin k, P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2) ∧
    ∀ᵐ ω ∂μ,
      (∀ (b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ)
        (h : (p : ℕ) → Fin k → EuclideanSpace ℝ (Fin p)),
        (∀ᶠ p in atTop, IsPrincipalFrame (Sig0 P.Barr Sf p) (b p)) →
        (∀ᶠ p in atTop, ∀ j, IsUnitEigvec (Scov P.Barr F (N.path ω) p) (h p j)
          (sortedEigN (Scov P.Barr F (N.path ω) p) j)) →
        (∀ᶠ p in atTop, (Hmat (h p))ᵀ * Hmat (h p) = 1) ∧
        Tendsto (fun p => (1 / 2 : ℝ) * frobSq (projH (h p) - projB (b p))) atTop
          (𝓝 (∑ j : Fin k, P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2)))) ∧
      Tendsto (fun p => ∑ j : Fin k,
          ellBulk P.Barr F (N.path ω) p / theta P.Barr F (N.path ω) p j) atTop
        (𝓝 (∑ j : Fin k, P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2))) := by
  have hfin : ∀ (p : ℕ) (b : Matrix (Fin p) (Fin k) ℝ) (h : Fin k → EuclideanSpace ℝ (Fin p)),
      bᵀ * b = 1 → (Hmat h)ᵀ * Hmat h = 1 →
      ∑ j, sinSqSub (h j) b = (1 / 2 : ℝ) * frobSq (projH h - projB b) ∧
      ∑ i, (1 - sortedEig ((bᵀ * Hmat h)ᵀ * (bᵀ * Hmat h)) i) =
        (1 / 2 : ℝ) * frobSq (projH h - projB b) := by
    intro p b h hb hH
    have hu : ∀ j, ‖h j‖ = 1 := fun j => by
      rw [← colVec_hmat h j]
      exact norm_colVec _ hH j
    have hF : (1 / 2 : ℝ) * frobSq (projH h - projB b) = k - frobSq (bᵀ * Hmat h) := by
      rw [projH, projB, frobSq_proj_sub b (Hmat h) hb hH]
      ring
    have hS : ∑ j, sinSqSub (h j) b = k - frobSq (bᵀ * Hmat h) := by
      rw [← sum_norm_projB_sq b hb h]
      have e : ∀ j, sinSqSub (h j) b = 1 - ‖Matrix.toEuclideanLin (projB b) (h j)‖ ^ 2 :=
        fun j => by
          rw [← (eq25_projection_norms b hb (h j) (hu j)).2]
          ring
      simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ⟨by rw [hS, hF], by rw [sum_one_sub_sortedEig_gram, hF]⟩
  refine ⟨hfin, sum_floor_pos P.hk P.δ2 P.δ2_pos (fun j => lam P.GB F j)
    (fun j => (hA6.2 j).le), ?_⟩
  obtain ⟨V, hV⟩ := exists_isEigenbasis
    (kmat_isHermitian (S := Sf) (transpose_eq_of_isHermitian P.GB_posDef.isHermitian))
  have hνex : ∀ j : Fin k, ∃ v, IsUnitEigvec (Nlim Sf P.GB V F) v
      (sortedEig (Nlim Sf P.GB V F) j) := fun j =>
    exists_unitEigvec_sortedEig (nlim_isHermitian F) j
  choose ν hν using hνex
  have hW : ∀ᵐ ω ∂μ, Tendsto (fun p => Wdual P.Barr F (N.path ω) p) atTop
      (𝓝 (Wlim P.GB F P.δ2)) := by
    filter_upwards [N.gram_limit hFact1 P.A3, N.cross_limit P] with ω h1 h2
    exact tendsto_wdual_of_parts (tendsto_w0p P F) h2 h1
  filter_upwards [hW, theorem1_error_decomposition hFact1 hFact2n hFact3n hFact2k hFact3k P Sf
      hSf hA5 F hA6 N V hV ν hν,
    theorem2_observable_floor hFact1 hFact2n hFact3n hFact2k hFact3k P Sf hSf hA5 F hA6 N V hV
      ν hν] with ω hω hT1 hT2
  refine ⟨fun b h hb hh => ?_, tendsto_finset_sum _ fun j _ => (hT2.2 j).2.1⟩
  have hH := eventually_hmat_orthonormal hFact2n P F hA6 hω h hh
  refine ⟨hH, ?_⟩
  have hlim : Tendsto (fun p => ∑ j, sinSqSub (h p j) (b p)) atTop
      (𝓝 (∑ j : Fin k, P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2))) :=
    tendsto_finset_sum _ fun j _ => (hT1 b h hb hh j).2.2.1
  refine hlim.congr' ?_
  filter_upwards [hH, hb] with p hp hbp
  exact (hfin p (b p) (h p) hbp.1 hp).1

/-! ## 7.2 In-subspace error is non-estimable from data -/

/-- **Theorem 3 (Rotation error cannot be estimated from data alone).**  Let `k ≥ 2` and
hold fixed the loadings, the path `F`, the noise, `δ²` and the eigenvalues of `K`; let `Σ`
range over the admissible factor covariances.
(i) The data `Y = BF + Z`, the sample directions `hⱼ` and the realized eigenvalues `λⱼ`
    do not involve `Σ` (in Lean: `Ymat`, `Scov`, `lam` take no covariance argument), hence
    neither does the out-of-subspace error `δ²/(nλⱼ+δ²)`; and every admissible `Σ` again
    satisfies the `Σ`-dependent assumptions (positive definite, Assumption 5), so
    Theorem 1 applies to it with `νⱼ(Σ)`.
(ii) The rotation error `sin²∠(νⱼ(Σ), eⱼ)` lies in `[0, 1]` and attains every value there.
(iii) Consequently the limiting estimation error (17) attains every value in
    `[δ²/(nλⱼ+δ²), 1]`.
"Attains `t`" means: some admissible `Σ` has `νⱼ(Σ)` defined, and every eigenbasis `V` of
`K(Σ)` and every `j`-th unit eigenvector `νⱼ(Σ)` of `N(Σ)` give the value `t`. -/
theorem theorem3_rotation_error_not_estimable
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k)
    (hk : 2 ≤ k) (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef)
    (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F)
    (j : Fin k) :
    -- (i)
    (∀ Sig : Matrix (Fin k) (Fin k) ℝ, Admissible Sf P.GB Sig →
      Sig.PosDef ∧ Assumption5 Sig P.GB) ∧
    -- (ii)
    (∀ (Sig V : Matrix (Fin k) (Fin k) ℝ) (ν : EuclideanSpace ℝ (Fin k)), Admissible Sf P.GB Sig →
      IsEigenbasis (Kmat Sig P.GB) V →
      IsUnitEigvec (Nlim Sig P.GB V F) ν (sortedEig (Nlim Sig P.GB V F) j) →
      sinSq ν (e j) ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∃ Sig : Matrix (Fin k) (Fin k) ℝ, Admissible Sf P.GB Sig ∧
      (∃ (V : Matrix (Fin k) (Fin k) ℝ) (ν : EuclideanSpace ℝ (Fin k)),
        IsEigenbasis (Kmat Sig P.GB) V ∧
        IsUnitEigvec (Nlim Sig P.GB V F) ν (sortedEig (Nlim Sig P.GB V F) j)) ∧
      ∀ (V : Matrix (Fin k) (Fin k) ℝ) (ν : EuclideanSpace ℝ (Fin k)),
        IsEigenbasis (Kmat Sig P.GB) V →
        IsUnitEigvec (Nlim Sig P.GB V F) ν (sortedEig (Nlim Sig P.GB V F) j) →
        sinSq ν (e j) = t) ∧
    -- (iii)
    (∀ t ∈ Set.Icc (P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2)) 1,
      ∃ Sig : Matrix (Fin k) (Fin k) ℝ, Admissible Sf P.GB Sig ∧
      (∃ (V : Matrix (Fin k) (Fin k) ℝ) (ν : EuclideanSpace ℝ (Fin k)),
        IsEigenbasis (Kmat Sig P.GB) V ∧
        IsUnitEigvec (Nlim Sig P.GB V F) ν (sortedEig (Nlim Sig P.GB V F) j)) ∧
      ∀ (V : Matrix (Fin k) (Fin k) ℝ) (ν : EuclideanSpace ℝ (Fin k)),
        IsEigenbasis (Kmat Sig P.GB) V →
        IsUnitEigvec (Nlim Sig P.GB V F) ν (sortedEig (Nlim Sig P.GB V F) j) →
        thm1Limit n P.δ2 (lam P.GB F j) (sinSq ν (e j)) = t) := by
  have hGB := P.GB_posDef
  refine ⟨fun Sig hSig => ⟨hSig.1, ?_⟩,
    fun Sig V ν hSig hV hν => sinSq_mem_Icc_of_unit hν.1 (by simp [e]),
    fun t ht => exists_sigma_sinSq hk hSf hGB hA5 hA6 j ht, fun t ht => ?_⟩
  · unfold Assumption5
    rw [hSig.2]
    exact hA5
  · have hl := hA6.2 j
    have hn : (0 : ℝ) < n := Nat.cast_pos.2 (n_pos_of_assumption6 hA6 j)
    have hδ := P.δ2_pos
    have hD : 0 < (n : ℝ) * lam P.GB F j + P.δ2 := by positivity
    have hnl : 0 < (n : ℝ) * lam P.GB F j := by positivity
    have hsum : P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2) +
        (n : ℝ) * lam P.GB F j / ((n : ℝ) * lam P.GB F j + P.δ2) = 1 := by
      field_simp
      ring
    have hs : (t - P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2)) /
        ((n : ℝ) * lam P.GB F j / ((n : ℝ) * lam P.GB F j + P.δ2)) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith [ht.1]) (by positivity)
      · rw [div_le_one (by positivity)]
        linarith [ht.2]
    obtain ⟨Sig, hadm, hex, hall⟩ := exists_sigma_sinSq hk hSf hGB hA5 hA6 j hs
    refine ⟨Sig, hadm, hex, fun V ν hV hν => ?_⟩
    rw [hall V ν hV hν, thm1Limit, mul_div_cancel₀ _ (by positivity)]
    ring

end PCError

end
