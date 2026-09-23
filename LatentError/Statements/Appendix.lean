import LatentError.Model
import LatentError.Lemmas.Duality
import LatentError.Lemmas.Noise
import LatentError.Lemmas.HardLeaves
import LatentError.Lemmas.Lemma5Leaves

/-!
# Statements of the supporting results (Appendices A–B)

Numbering follows the Sept 14, 2026 version of the paper.  The statements were frozen
before any proof search (`harness/freeze.py`); all of them are now proved.

Conventions (following the Ono/AxiomProver protocol):
* The background facts `Fact1_SLLN`, `Fact2_Weyl m`, `Fact3_EigCont m` are explicit
  hypotheses, never axioms.  A supporting result takes the facts that its proof in the
  paper invokes; the headline results in `Main.lean` take all three, at dimensions `n`
  and `k`.
* Eigenvectors are never pinned by sign.  Statements quantify over *every* admissible
  choice and conclude sign-free quantities (`sinSq`, `|⟪·,·⟫|`).  Where the paper fixes a
  sign convention (Proposition 2), the convention is a hypothesis and its satisfiability is
  part of the conclusion.
* "Conditional on `F`, almost surely as `p → ∞`" is `∀ᵐ ω ∂μ` over a `NoiseModel` on
  `(Ω, μ)` with `F` a fixed matrix (see `Model.lean`).
-/

open scoped Matrix Topology MatrixOrder ProbabilityTheory
open Filter MeasureTheory ProbabilityTheory

noncomputable section

set_option linter.unusedVariables false

namespace PCError

variable {k n : ℕ}

/-! ## A.1 Matrix preliminaries -/

/-- **Lemma 1 (Gram duality).**  `A Aᵀ` and `Aᵀ A` have the same zero-padded sorted
spectrum (so their `j`-th nonzero eigenvalues agree), and for a nonzero eigenvalue `λ`
the maps `v ↦ Aᵀ v/√λ` and `u ↦ A u/√λ` carry unit eigenvectors to unit eigenvectors. -/
theorem lemma1_gram_duality {m l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ) :
    sortedEigN (A * Aᵀ) = sortedEigN (Aᵀ * A) ∧
    (∀ (v : EuclideanSpace ℝ (Fin m)) (lam : ℝ), lam ≠ 0 → IsUnitEigvec (A * Aᵀ) v lam →
      IsUnitEigvec (Aᵀ * A) ((1 / Real.sqrt lam) • Matrix.toEuclideanLin Aᵀ v) lam) ∧
    (∀ (u : EuclideanSpace ℝ (Fin l)) (lam : ℝ), lam ≠ 0 → IsUnitEigvec (Aᵀ * A) u lam →
      IsUnitEigvec (A * Aᵀ) ((1 / Real.sqrt lam) • Matrix.toEuclideanLin A u) lam) := by
  refine ⟨sortedEigN_mul_transpose A, fun v lam hlam hv => gram_eigvec A v lam hlam hv, ?_⟩
  intro u lam hlam hu
  have h := gram_eigvec Aᵀ u lam hlam (by rwa [Matrix.transpose_transpose])
  rwa [Matrix.transpose_transpose] at h

/-- **Lemma 2 (i) (Eigenpair convergence).**  Let symmetric `A⁽ᵖ⁾ → A` and let the
`j`-th largest eigenvalue `ζ` of `A` be simple, with unit eigenvector `v`.  Then for large
`p` the `j`-th largest eigenvalue `ζ⁽ᵖ⁾` of `A⁽ᵖ⁾` is simple, `ζ⁽ᵖ⁾ → ζ`, and every choice
of unit eigenvectors `v⁽ᵖ⁾` for `ζ⁽ᵖ⁾` satisfies `|⟪v⁽ᵖ⁾, v⟫| → 1`. -/
theorem lemma2_i_eigenpair_convergence {m : ℕ} (hFact2 : Fact2_Weyl m)
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
  exact eigpair_convergence hFact2 A Ainf hA hAinf hlim j hsimple v hv

/-- **Lemma 2 (ii) (Sign pinning).**  If unit vectors satisfy `|⟪u⁽ᵖ⁾, u⟫| → 1`, then
`⟪u⁽ᵖ⁾, u⟫` is eventually nonzero and `sign⟪u⁽ᵖ⁾, u⟫ · u⁽ᵖ⁾ → u`. -/
theorem lemma2_ii_sign_pinning {m : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin m))
    (u0 : EuclideanSpace ℝ (Fin m)) (hu : ∀ p, ‖u p‖ = 1) (hu0 : ‖u0‖ = 1)
    (hlim : Tendsto (fun p => |inner ℝ (u p) u0|) atTop (𝓝 1)) :
    (∀ᶠ p in atTop, inner ℝ (u p) u0 ≠ 0) ∧
    Tendsto (fun p => Real.sign (inner ℝ (u p) u0) • u p) atTop (𝓝 u0) := by
  exact sign_pinning u u0 hu hu0 hlim

/-! ## A.2 The principal coordinate chart at finite `p` -/

/-- **Lemma 3 (Change of basis).**  For `B` of rank `k` and `b` with orthonormal columns
spanning `col(B)`:
1. `C = (BᵀB)⁻¹Bᵀb` is the unique matrix with `B C = b`;
2. `C⁻¹ = bᵀB` (so `ϕ = C⁻¹ f = bᵀ B f`);
3. if `b` is a principal frame of `Σ₀ = B Σ_f Bᵀ`, then
   `𝔼[ϕϕᵀ] = bᵀ B Σ_f Bᵀ b = Δ₀`, the diagonal of the top-`k` eigenvalues of `Σ₀`. -/
theorem lemma3_change_of_basis {p : ℕ} (B b : Matrix (Fin p) (Fin k) ℝ)
    (Sf : Matrix (Fin k) (Fin k) ℝ) (hB : B.rank = k) (hb : bᵀ * b = 1)
    (hcol : LinearMap.range B.mulVecLin = LinearMap.range b.mulVecLin) :
    let C := (Bᵀ * B)⁻¹ * Bᵀ * b
    (B * C = b ∧ ∀ C' : Matrix (Fin k) (Fin k) ℝ, B * C' = b → C' = C) ∧
    (bᵀ * B * C = 1 ∧ C * (bᵀ * B) = 1) ∧
    (IsPrincipalFrame (B * Sf * Bᵀ) b →
      bᵀ * B * Sf * Bᵀ * b = Matrix.diagonal (fun j : Fin k => sortedEigN (B * Sf * Bᵀ) j)) := by
  intro C
  have hU := isUnit_transpose_mul_of_rank hB
  obtain ⟨M, hM⟩ := exists_mul_eq_of_range_le hcol.ge
  have hBC : B * C = b := mul_inv_gram_mul hU hM
  have h1 : bᵀ * B * C = 1 := transpose_mul_mul_eq_one hb hBC
  refine ⟨⟨hBC, fun C' h' => eq_of_mul_eq_gram hU h'⟩, ⟨h1, mul_transpose_mul_eq_one h1⟩,
    fun hf => ?_⟩
  simpa only [Matrix.mul_assoc] using transpose_mul_frame hf

/-- **Proposition 1 (Principal coordinates and the eigenbasis `V⁽ᵖ⁾`).**  For all large
`p`:
1. `K⁽ᵖ⁾ = Σ_f^{1/2} G_B⁽ᵖ⁾ Σ_f^{1/2}` has distinct positive eigenvalues `μ⁽ᵖ⁾`, the
   nonzero spectrum of `Σ₀` is `p μ⁽ᵖ⁾` (so `Σ₀ = b Δ₀ bᵀ` with `Δ₀ = p diag μ⁽ᵖ⁾`),
   principal frames `b` exist, and for each of them `V⁽ᵖ⁾ = Σ_f^{1/2}Bᵀb Δ₀^{-1/2}` is the
   unique orthogonal matrix with `Σ_f^{1/2} Bᵀ b = V⁽ᵖ⁾ Δ₀^{1/2}` (eq. (46)); it is an
   ordered eigenbasis of `K⁽ᵖ⁾`;
2. `C = Σ_f^{1/2} V⁽ᵖ⁾ Δ₀^{-1/2}` satisfies `B C = b` (eq. (47)). -/
theorem prop1_principal_coordinates (hFact2k : Fact2_Weyl k) (P : LoadingParams k n)
    (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB) :
    ∀ᶠ p in atTop,
      (StrictAnti (sortedEig (Kmat Sf (GBp P.Barr p))) ∧
        ∀ j, 0 < sortedEig (Kmat Sf (GBp P.Barr p)) j) ∧
      (∀ j : Fin k, sortedEigN (Sig0 P.Barr Sf p) j =
        (p : ℝ) * sortedEig (Kmat Sf (GBp P.Barr p)) j) ∧
      (∀ i : ℕ, k ≤ i → sortedEigN (Sig0 P.Barr Sf p) i = 0) ∧
      (∃ b : Matrix (Fin p) (Fin k) ℝ, IsPrincipalFrame (Sig0 P.Barr Sf p) b) ∧
      ∀ b : Matrix (Fin p) (Fin k) ℝ, IsPrincipalFrame (Sig0 P.Barr Sf p) b →
        b * Matrix.diagonal (fun j : Fin k => sortedEigN (Sig0 P.Barr Sf p) j) * bᵀ =
            Sig0 P.Barr Sf p ∧
        (∀ V : Matrix (Fin k) (Fin k) ℝ,
          (Vᵀ * V = 1 ∧ CFC.sqrt Sf * (Bmat P.Barr p)ᵀ * b = V * Delta0Sqrt P.Barr Sf p) ↔
            V = Vpn P.Barr Sf p b) ∧
        IsEigenbasis (Kmat Sf (GBp P.Barr p)) (Vpn P.Barr Sf p b) ∧
        Bmat P.Barr p * (CFC.sqrt Sf * Vpn P.Barr Sf p b * (Delta0Sqrt P.Barr Sf p)⁻¹) = b := by
  filter_upwards [eventually_kp_simple hFact2k P hA5, eventually_pmu_pos hFact2k P hA5]
    with p hK ⟨hp, hpos⟩
  refine ⟨hK, fun j => ?_, fun i hi => ?_, exists_frame hSf hp hpos, fun b hb => ?_⟩
  · rw [sortedEigN_sig0 P.Barr hSf hp, sortedEigN, dif_pos j.2]
  · rw [sortedEigN_sig0 P.Barr hSf hp, sortedEigN, dif_neg (by omega), mul_zero]
  · obtain ⟨-, -, e3, -, e5⟩ := frame_facts hSf hp hpos hb
    exact ⟨e3, frame_V_unique hSf hp hpos hb, e5, frame_C hSf hp hpos hb⟩

/-! ## A.3 The systematic dual Gram matrices in the limit -/

/-- **Proposition 2 (Limits of the systematic dual Grams).**  Fix an ordered eigenbasis
`V` of `K`.
(i) For every principal frame, `ΦᵀΦ/(np) = Fᵀ G_B⁽ᵖ⁾ F/n` (eq. (52)), and this tends to
    `W₀ = Fᵀ G_B F/n`.
The sign convention `⟪V⁽ᵖ⁾_{·j}, V_{·j}⟫ ≥ 0` can be met by principal frames, and under it
(ii) `V⁽ᵖ⁾ → V`, `μ⁽ᵖ⁾ → μ`, `Φ̄ = Φ/√p → Φ̄^∞` of eq. (50), and `N⁽ᵖ⁾ → N` of eq. (51). -/
theorem prop2_systematic_limits (hFact2k : Fact2_Weyl k) (P : LoadingParams k n)
    (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB)
    (F : Matrix (Fin k) (Fin n) ℝ) (V : Matrix (Fin k) (Fin k) ℝ)
    (hV : IsEigenbasis (Kmat Sf P.GB) V) :
    (∀ᶠ p in atTop, ∀ b : Matrix (Fin p) (Fin k) ℝ, IsPrincipalFrame (Sig0 P.Barr Sf p) b →
      (1 / ((n : ℝ) * p)) • ((PhiMat b (Bmat P.Barr p) F)ᵀ * PhiMat b (Bmat P.Barr p) F) =
        (1 / (n : ℝ)) • (Fᵀ * GBp P.Barr p * F)) ∧
    Tendsto (fun p : ℕ => (1 / (n : ℝ)) • (Fᵀ * GBp P.Barr p * F)) atTop (𝓝 (W0 P.GB F)) ∧
    (∃ b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ,
      (∀ᶠ p in atTop, IsPrincipalFrame (Sig0 P.Barr Sf p) (b p)) ∧
      ∀ᶠ p in atTop, ∀ j, 0 ≤ ∑ i, Vpn P.Barr Sf p (b p) i j * V i j) ∧
    ∀ b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ,
      (∀ᶠ p in atTop, IsPrincipalFrame (Sig0 P.Barr Sf p) (b p)) →
      (∀ᶠ p in atTop, ∀ j, 0 ≤ ∑ i, Vpn P.Barr Sf p (b p) i j * V i j) →
      Tendsto (fun p => Vpn P.Barr Sf p (b p)) atTop (𝓝 V) ∧
      (∀ j, Tendsto (fun p => sortedEig (Kmat Sf (GBp P.Barr p)) j) atTop
        (𝓝 (sortedEig (Kmat Sf P.GB) j))) ∧
      Tendsto (fun p : ℕ => (1 / Real.sqrt p) • PhiMat (b p) (Bmat P.Barr p) F) atTop
        (𝓝 (PhiBarInf Sf P.GB V F)) ∧
      Tendsto (fun p : ℕ => Npn (b p) (Bmat P.Barr p) F) atTop (𝓝 (Nlim Sf P.GB V F)) := by
  refine ⟨?_, tendsto_w0p P F, exists_conv_frames hFact2k P hSf hA5 V, fun b hb hsign =>
    ⟨tendsto_vpn hFact2k P hSf hA5 hV hb hsign, tendsto_sortedEig_kp hFact2k P Sf,
      tendsto_phibar hFact2k P hSf hA5 F hV hb hsign, tendsto_npn hFact2k P hSf hA5 F hV hb hsign⟩⟩
  filter_upwards [eventually_pmu_pos hFact2k P hA5] with p ⟨hp, hpos⟩
  exact fun b hb => phi_gram hSf hp hpos hb F

/-- **Remark after Proposition 2.**  With `Λ = diag μ`, `Q = Λ^{1/2} Vᵀ Σ_f^{-1/2}` and
`Σ̂_f = F Fᵀ/n`: `Q Σ̂_f Qᵀ = N`, `Q Σ_f Qᵀ = Λ`, and `QᵀQ = G_B`. -/
theorem prop2_remark (Sf GB V : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (hSf : Sf.PosDef) (hGB : GB.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) :
    Qmat Sf GB V * ((1 / (n : ℝ)) • (F * Fᵀ)) * (Qmat Sf GB V)ᵀ = Nlim Sf GB V F ∧
    Qmat Sf GB V * Sf * (Qmat Sf GB V)ᵀ = LamDiag Sf GB ∧
    (Qmat Sf GB V)ᵀ * Qmat Sf GB V = GB := by
  exact ⟨qmat_sigmaHat F, qmat_sf_qmat hSf hA5 hV, qmat_transpose_mul hSf hA5 hV⟩

/-- **Corollary 2 (Gram duality of the realized systematic matrices).**
`(Φ̄^∞)ᵀΦ̄^∞/n = W₀`; `N` and `W₀` have the same (zero-padded, sorted) spectrum; and for a
unit eigenvector `wⱼ` of `W₀` at `λⱼ`, `νⱼ := Φ̄^∞ wⱼ/√(nλⱼ)` is a unit eigenvector of `N` at
`λⱼ`, i.e. `Φ̄^∞ wⱼ = √(nλⱼ) νⱼ` (eq. (53)); every unit eigenvector of `N` at `λⱼ` is `±νⱼ`. -/
theorem cor2_realized_duality (Sf GB V : Matrix (Fin k) (Fin k) ℝ)
    (F : Matrix (Fin k) (Fin n) ℝ) (hSf : Sf.PosDef) (hGB : GB.PosDef)
    (hA5 : Assumption5 Sf GB) (hA6 : Assumption6 GB F) (hV : IsEigenbasis (Kmat Sf GB) V) :
    (1 / (n : ℝ)) • ((PhiBarInf Sf GB V F)ᵀ * PhiBarInf Sf GB V F) = W0 GB F ∧
    sortedEigN (Nlim Sf GB V F) = sortedEigN (W0 GB F) ∧
    ∀ (j : Fin k) (w : EuclideanSpace ℝ (Fin n)), IsUnitEigvec (W0 GB F) w (lam GB F j) →
      IsUnitEigvec (Nlim Sf GB V F)
          ((1 / Real.sqrt ((n : ℝ) * lam GB F j)) •
            Matrix.toEuclideanLin (PhiBarInf Sf GB V F) w) (lam GB F j) ∧
      ∀ ν, IsUnitEigvec (Nlim Sf GB V F) ν (lam GB F j) →
        Matrix.toEuclideanLin (PhiBarInf Sf GB V F) w = Real.sqrt ((n : ℝ) * lam GB F j) • ν ∨
        Matrix.toEuclideanLin (PhiBarInf Sf GB V F) w =
          -(Real.sqrt ((n : ℝ) * lam GB F j) • ν) := by
  refine ⟨phiBarInf_gram hSf hA5 hV F, sortedEigN_nlim hSf hA5 hV F, fun j w hw => ?_⟩
  have hl := hA6.2 j
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (n_pos_of_assumption6 hA6 j)
  have hsq : Real.sqrt ((n : ℝ) * lam GB F j) ≠ 0 := (Real.sqrt_pos.2 (mul_pos hn hl)).ne'
  have hν₀ := nlim_eigvec_of_w0 hSf hA5 hV F hl hw
  refine ⟨hν₀, fun ν hν => ?_⟩
  have hsimple : ∀ i, i ≠ j → sortedEig (Nlim Sf GB V F) i ≠ sortedEig (Nlim Sf GB V F) j := by
    intro i hij
    rw [sortedEig_nlim hSf hA5 hV, sortedEig_nlim hSf hA5 hV]
    exact hA6.1.injective.ne hij
  rw [← sortedEig_nlim hSf hA5 hV F j] at hν₀ hν
  rcases unitEigvec_eq_or_eq_neg (nlim_isHermitian F) hsimple hν₀ hν with h | h <;>
    rw [sortedEig_nlim hSf hA5 hV F j] at h
  · left
    rw [h, smul_smul, mul_one_div_cancel hsq, one_smul]
  · right
    rw [h, smul_neg, neg_neg, smul_smul, mul_one_div_cancel hsq, one_smul]

/-- **Corollary 3 (Large-`n` limit of `N`).**  Stated path-wise (which implies the paper's
almost-sure version): if the factor draws satisfy `F⁽ⁿ⁾F⁽ⁿ⁾ᵀ/n → Σ_f`, then
`N⁽ⁿ⁾ → diag(μ)`, the realized eigenvalues `λⱼ⁽ⁿ⁾` tend to `μⱼ` (used in the remark after
Theorem 1), and every choice of `j`-th unit eigenvectors `νⱼ⁽ⁿ⁾` of `N⁽ⁿ⁾` has
`sin²∠(νⱼ⁽ⁿ⁾, eⱼ) → 0`. -/
theorem cor3_large_n (hFact2k : Fact2_Weyl k) (Sf GB V : Matrix (Fin k) (Fin k) ℝ)
    (hSf : Sf.PosDef) (hGB : GB.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) (f : ℕ → Fin k → ℝ)
    (hf : Tendsto (fun n : ℕ => (1 / (n : ℝ)) • (Fcols f n * (Fcols f n)ᵀ)) atTop (𝓝 Sf)) :
    Tendsto (fun n => Nlim Sf GB V (Fcols f n)) atTop (𝓝 (LamDiag Sf GB)) ∧
    (∀ j : Fin k, Tendsto (fun n => lam GB (Fcols f n) j) atTop
      (𝓝 (sortedEig (Kmat Sf GB) j))) ∧
    ∀ (j : Fin k) (ν : ℕ → EuclideanSpace ℝ (Fin k)),
      (∀ᶠ n in atTop, IsUnitEigvec (Nlim Sf GB V (Fcols f n)) (ν n)
        (sortedEig (Nlim Sf GB V (Fcols f n)) j)) →
      Tendsto (fun n => sinSq (ν n) (e j)) atTop (𝓝 0) := by
  exact ⟨nlim_tendsto_lamDiag hSf hA5 hV f hf, lam_tendsto_mu hFact2k hSf hA5 hV f hf,
    fun j ν hν => nu_tendsto_axis hFact2k hSf hA5 hV f hf j ν hν⟩

/-- **Remark after Corollary 3, item 1.**  If the factor draws `f⁽ˡ⁾` are independent with
common second moments `Σ_f` and uniformly bounded fourth moments, then
`F⁽ⁿ⁾F⁽ⁿ⁾ᵀ/n → Σ_f` almost surely (via Kolmogorov's strong law, Fact 1).
(Item 2, the stationary ergodic case, is only sketched in the paper and is not stated.) -/
theorem cor3_remark_independent_factors (hFact1 : Fact1_SLLN) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Sf : Matrix (Fin k) (Fin k) ℝ)
    (f : ℕ → Ω → Fin k → ℝ) (hmeas : ∀ l, Measurable (f l)) (hindep : iIndepFun f μ)
    (hmom : ∀ l a, MemLp (fun ω => f l ω a) 4 μ)
    (hcov : ∀ l a b, μ[fun ω => f l ω a * f l ω b] = Sf a b)
    (κf : ℝ) (h4 : ∀ l, μ[fun ω => (∑ a, f l ω a ^ 2) ^ 2] ≤ κf) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (1 / (n : ℝ)) •
      (Fcols (fun l => f l ω) n * (Fcols (fun l => f l ω) n)ᵀ)) atTop (𝓝 Sf) := by
  have h : ∀ᵐ ω ∂μ, ∀ a b, Tendsto (fun n : ℕ => (1 / (n : ℝ)) *
      ∑ l ∈ Finset.range n, f l ω a * f l ω b) atTop (𝓝 (Sf a b)) :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun b =>
      factor_entry_slln hFact1 μ Sf f hmeas hindep hmom hcov κf h4 a b
  filter_upwards [h] with ω hω
  refine tendsto_matrix_of_entries fun a b => ?_
  simpa only [Matrix.smul_apply, smul_eq_mul, fcols_mul_transpose_apply] using hω a b

/-! ## A.4 The observable dual Gram matrix in the limit -/

/-- **Lemma 4 (Specific return concentration).**  For deterministic unit vectors
`a⁽ᵖ⁾ ∈ ℝᵖ` and a fixed observation `l`, `a⁽ᵖ⁾ᵀ Z_{·l}/√p → 0` almost surely under the
conditional law of the noise. -/
theorem lemma4_specific_concentration {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {var : ℕ → Fin n → ℝ} {κ4 : ℝ} (N : NoiseModel n var κ4 Ω μ)
    (a : (p : ℕ) → EuclideanSpace ℝ (Fin p)) (ha : ∀ᶠ p in atTop, ‖a p‖ = 1) (l : Fin n) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (∑ i : Fin p, a p i * N.Z i l ω) / Real.sqrt p) atTop
      (𝓝 0) := by
  exact N.concentration a ha l

/-- The finite-`p` identity `‖ΠZ‖_F = ‖bᵀZ‖_F` for `b` with orthonormal columns
(Proposition 3(b)). -/
theorem prop3_b_frobenius_identity {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (Z : Matrix (Fin p) (Fin n) ℝ) : frobSq (projB b * Z) = frobSq (bᵀ * Z) := by
  rw [frobSq_eq_trace, frobSq_eq_trace]
  simp only [projB, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc bᵀ b, hb, Matrix.one_mul]

/-- **Proposition 3 (Limit of the observable dual `W⁽ᵖ⁾`).**  Conditional on `F`, almost
surely as `p → ∞`:
(a) `ZᵀZ/(np) → (δ²/n) Iₙ` in spectral norm;
(b) for every deterministic sequence of orthonormal `k`-frames `b⁽ᵖ⁾`,
    `‖bᵀZ‖_F = o(√p)`;
(c) `W⁽ᵖ⁾ → W = W₀ + (δ²/n) Iₙ` in spectral norm; the sorted spectrum of `W` is
    `λ₁ + δ²/n, …, λ_k + δ²/n, δ²/n, …, δ²/n`, with the eigenvectors of `W₀`;
(d) `θⱼ⁽ᵖ⁾ → λⱼ + δ²/n > 0`, and every choice of unit eigenvectors `wⱼ⁽ᵖ⁾` of `W⁽ᵖ⁾` at
    `θⱼ⁽ᵖ⁾` satisfies `|⟪wⱼ⁽ᵖ⁾, wⱼ⟫| → 1`. -/
theorem prop3_observable_dual (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n)
    (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef)
    (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (N : NoiseModel n P.var P.κ4 Ω μ) :
    -- (a)
    (∀ᵐ ω ∂μ, Tendsto (fun p : ℕ =>
      opNorm ((1 / ((n : ℝ) * p)) • ((truncRows (N.path ω) p)ᵀ * truncRows (N.path ω) p) -
        (P.δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ))) atTop (𝓝 0)) ∧
    -- (b)
    (∀ b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ, (∀ᶠ p in atTop, (b p)ᵀ * b p = 1) →
      ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ =>
        Real.sqrt (frobSq ((b p)ᵀ * truncRows (N.path ω) p)) / Real.sqrt p) atTop (𝓝 0)) ∧
    -- (c)
    (∀ᵐ ω ∂μ, Tendsto (fun p : ℕ =>
      opNorm (Wdual P.Barr F (N.path ω) p - Wlim P.GB F P.δ2)) atTop (𝓝 0)) ∧
    (∀ i : Fin n, (i : ℕ) < k → sortedEig (Wlim P.GB F P.δ2) i = lam P.GB F i + P.δ2 / n) ∧
    (∀ i : Fin n, k ≤ (i : ℕ) → sortedEig (Wlim P.GB F P.δ2) i = P.δ2 / n) ∧
    (∀ (j : Fin k) (w : EuclideanSpace ℝ (Fin n)), IsUnitEigvec (W0 P.GB F) w (lam P.GB F j) →
      IsUnitEigvec (Wlim P.GB F P.δ2) w (lam P.GB F j + P.δ2 / n)) ∧
    -- (d)
    (∀ᵐ ω ∂μ, ∀ j : Fin k,
      Tendsto (fun p => theta P.Barr F (N.path ω) p j) atTop (𝓝 (lam P.GB F j + P.δ2 / n)) ∧
      0 < lam P.GB F j + P.δ2 / n ∧
      ∀ wp : ℕ → EuclideanSpace ℝ (Fin n),
        (∀ᶠ p in atTop, IsUnitEigvec (Wdual P.Barr F (N.path ω) p) (wp p)
          (theta P.Barr F (N.path ω) p j)) →
        ∀ w, IsUnitEigvec (W0 P.GB F) w (lam P.GB F j) →
          Tendsto (fun p => |inner ℝ (wp p) w|) atTop (𝓝 1)) := by
  have hW : ∀ᵐ ω ∂μ, Tendsto (fun p => Wdual P.Barr F (N.path ω) p) atTop
      (𝓝 (Wlim P.GB F P.δ2)) := by
    filter_upwards [N.gram_limit hFact1 P.A3, N.cross_limit P] with ω h1 h2
    exact tendsto_wdual_of_parts (tendsto_w0p P F) h2 h1
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by have := P.hkn; omega)
  refine ⟨N.gram_limit_opNorm hFact1 P.A3, fun b hb => N.frob_limit b hb, ?_,
    fun i hi => sortedEig_wlim_lt P.GB_posDef F P.δ2 i hi,
    fun i hi => sortedEig_wlim_ge P.GB_posDef F P.δ2 i hi,
    fun j w hw => isUnitEigvec_wlim F P.δ2 w _ hw, ?_⟩
  · filter_upwards [hW] with ω hω
    exact tendsto_opNorm_sub hω
  · filter_upwards [hW] with ω hω
    intro j
    exact ⟨theta_limit hFact2n P F hω j, add_pos (hA6.2 j) (div_pos P.δ2_pos hn),
      fun wp hwp w hw => wdual_eigvec_limit hFact2n P F hA6 hω j wp hwp w hw⟩

/-! ## A.5 A consequence of the model assumptions -/

/-- **Lemma 5 (All-pairs uncorrelatedness and the per-date covariance).**  In the joint
model: (1) every `Z_{il} f_a⁽ᵐ⁾` is integrable with mean zero (eq. (56)); (2) the
observation `y⁽ˡ⁾ = B f⁽ˡ⁾ + z⁽ˡ⁾` has `𝔼[y⁽ˡ⁾y⁽ˡ⁾ᵀ] = B Σ_f Bᵀ + diag(δ²_{1,l}, …, δ²_{p,l})`
(eq. (57)). -/
theorem lemma5_uncorrelated {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (J : JointModel k n Ω μ) :
    (∀ (i : ℕ) (a : Fin k) (l m : Fin n),
      Integrable (fun ω => J.Z i l ω * J.fc a m ω) μ ∧
      μ[fun ω => J.Z i l ω * J.fc a m ω] = 0) ∧
    ∀ (l : Fin n) (p : ℕ) (i i' : Fin p),
      μ[fun ω => (∑ a, J.Barr i a * J.fc a l ω + J.Z i l ω) *
          (∑ a, J.Barr i' a * J.fc a l ω + J.Z i' l ω)] =
        (Sig0 J.Barr J.Sf p + Matrix.diagonal (fun i : Fin p => J.var i l)) i i' := by
  refine ⟨fun i a l m => ⟨J.integrable_Z_mul_fc i l a m, J.integral_Z_mul_fc i l a m⟩, ?_⟩
  intro l p i i'
  have hexp : (fun ω => (∑ a, J.Barr i a * J.fc a l ω + J.Z i l ω) *
      (∑ a, J.Barr i' a * J.fc a l ω + J.Z i' l ω)) =
      fun ω => (∑ a, ∑ b, J.Barr i a * J.Barr i' b * (J.fc a l ω * J.fc b l ω)) +
        (∑ a, J.Barr i a * (J.fc a l ω * J.Z i' l ω)) +
        (∑ b, J.Barr i' b * (J.Z i l ω * J.fc b l ω)) + J.Z i l ω * J.Z i' l ω := by
    funext ω
    exact prod_expand _ _ _ _ _ _
  have hI1 : Integrable (fun ω => ∑ a, ∑ b, J.Barr i a * J.Barr i' b *
      (J.fc a l ω * J.fc b l ω)) μ :=
    integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      ((J.integrable_fc_mul a b l l).const_mul _)
  have hI2 : Integrable (fun ω => ∑ a, J.Barr i a * (J.fc a l ω * J.Z i' l ω)) μ :=
    integrable_finset_sum _ fun a _ =>
      (((J.integrable_Z_mul_fc i' l a l).congr
        (Filter.Eventually.of_forall fun ω => mul_comm _ _)).const_mul _)
  have hI3 : Integrable (fun ω => ∑ b, J.Barr i' b * (J.Z i l ω * J.fc b l ω)) μ :=
    integrable_finset_sum _ fun b _ => ((J.integrable_Z_mul_fc i l b l).const_mul _)
  have hI4 : Integrable (fun ω => J.Z i l ω * J.Z i' l ω) μ := J.integrable_Z_mul_Z i i' l
  rw [hexp, integral_add (by exact (hI1.add hI2).add hI3) hI4,
    integral_add (by exact hI1.add hI2) hI3, integral_add hI1 hI2]
  have e1 : μ[fun ω => ∑ a, ∑ b, J.Barr i a * J.Barr i' b * (J.fc a l ω * J.fc b l ω)] =
      ∑ a, ∑ b, J.Barr i a * J.Sf a b * J.Barr i' b := by
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      ((J.integrable_fc_mul a b l l).const_mul _)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ fun b _ => ((J.integrable_fc_mul a b l l).const_mul _)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, J.A1_cov a b l]
    ring
  have e2 : μ[fun ω => ∑ a, J.Barr i a * (J.fc a l ω * J.Z i' l ω)] = 0 := by
    rw [integral_finset_sum _ fun a _ =>
      (((J.integrable_Z_mul_fc i' l a l).congr
        (Filter.Eventually.of_forall fun ω => mul_comm _ _)).const_mul _)]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [integral_const_mul]
    have : μ[fun ω => J.fc a l ω * J.Z i' l ω] = μ[fun ω => J.Z i' l ω * J.fc a l ω] :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
    rw [this, J.integral_Z_mul_fc i' l a l, mul_zero]
  have e3 : μ[fun ω => ∑ b, J.Barr i' b * (J.Z i l ω * J.fc b l ω)] = 0 := by
    rw [integral_finset_sum _ fun b _ => ((J.integrable_Z_mul_fc i l b l).const_mul _)]
    exact Finset.sum_eq_zero fun b _ => by
      rw [integral_const_mul, J.integral_Z_mul_fc i l b l, mul_zero]
  rw [e1, e2, e3, Matrix.add_apply, sig0_apply, Matrix.diagonal_apply]
  by_cases hii : i = i'
  · subst hii
    have : (fun ω => J.Z i l ω * J.Z i l ω) = fun ω => J.Z i l ω ^ 2 := by
      funext ω; ring
    rw [this, J.integral_Z_sq, if_pos rfl]
    ring
  · rw [J.integral_Z_mul_Z_of_ne l (fun h => hii (Fin.ext h)), if_neg hii]
    ring

/-! ## B. Indeterminacy of the principal frame -/

/-- **Lemma 6 (Indeterminacy of the principal coordinates).**
(i) The admissible factor covariances are exactly `Σ_O = G_B^{-1/2} Oᵀ Λ O G_B^{-1/2}`,
    `O ∈ O(k)` (eq. (61)).
(ii) For every `O ∈ O(k)` there is an ordered eigenbasis `V` of `K(Σ_O)` (the matched sign
    choice) with `N(Σ_O) = O M̂ Oᵀ` (eq. (62)).
Also, `M̂` has the same spectrum as `W₀` (the paragraph before the lemma). -/
theorem lemma6_indeterminacy (Sf GB : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef)
    (hGB : GB.PosDef) (hA5 : Assumption5 Sf GB) :
    (∀ Sig : Matrix (Fin k) (Fin k) ℝ, Admissible Sf GB Sig ↔
      ∃ O ∈ Matrix.orthogonalGroup (Fin k) ℝ, Sig = SigmaO GB (LamDiag Sf GB) O) ∧
    ∀ F : Matrix (Fin k) (Fin n) ℝ, Assumption6 GB F →
      sortedEigN (Mhat GB F) = sortedEigN (W0 GB F) ∧
      ∀ O ∈ Matrix.orthogonalGroup (Fin k) ℝ,
        ∃ V, IsEigenbasis (Kmat (SigmaO GB (LamDiag Sf GB) O) GB) V ∧
          Nlim (SigmaO GB (LamDiag Sf GB) O) GB V F = O * Mhat GB F * Oᵀ := by
  refine ⟨fun Sig => ⟨admissible_eq_sigmaO hSf hGB hA5, ?_⟩,
    fun F hF => ⟨sortedEigN_mhat hGB F, fun O hO => exists_eigenbasis_nlim_sigmaO hSf hGB hA5 F hO⟩⟩
  rintro ⟨O, hO, rfl⟩
  exact sigmaO_admissible hSf hGB hA5 hO

end PCError

end
