import LatentError.Facts.SLLN
import LatentError.Facts.EigCont
import LatentError.Statements.Main

/-!
# The paper's results with the background facts discharged

`Fact1_SLLN`, `Fact2_Weyl` and `Fact3_EigCont` are proved in `LatentError/Facts/`, so every
statement that took them as hypotheses can be restated without them.  These are the same
theorems as in `Statements/`, applied to `fact1_slln`, `fact2_weyl` and `fact3_eigCont`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory Matrix MatrixOrder

noncomputable section

set_option linter.unusedVariables false

namespace PCError

variable {k n : ℕ}

/-- `theorem1_error_decomposition` with the three background facts discharged. -/
theorem theorem1_error_decomposition_unconditional
    (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F) {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (N : NoiseModel n P.var P.κ4 Ω μ) (V : Matrix (Fin k) (Fin k) ℝ) (hV : IsEigenbasis (Kmat Sf P.GB) V) (ν : Fin k → EuclideanSpace ℝ (Fin k)) (hν : ∀ j, IsUnitEigvec (Nlim Sf P.GB V F) (ν j) (sortedEig (Nlim Sf P.GB V F) j)) :
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
          atTop (𝓝 (sinSq (ν j) (e j))) :=
  theorem1_error_decomposition fact1_slln (fact2_weyl n) (fact3_eigCont n) (fact2_weyl k) (fact3_eigCont k) P Sf hSf hA5 F hA6 N V hV ν hν

/-- `theorem2_observable_floor` with the three background facts discharged. -/
theorem theorem2_observable_floor_unconditional
    (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F) {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (N : NoiseModel n P.var P.κ4 Ω μ) (V : Matrix (Fin k) (Fin k) ℝ) (hV : IsEigenbasis (Kmat Sf P.GB) V) (ν : Fin k → EuclideanSpace ℝ (Fin k)) (hν : ∀ j, IsUnitEigvec (Nlim Sf P.GB V F) (ν j) (sortedEig (Nlim Sf P.GB V F) j)) :
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
          sinSq (ν j) (e j) = 0) :=
  theorem2_observable_floor fact1_slln (fact2_weyl n) (fact3_eigCont n) (fact2_weyl k) (fact3_eigCont k) P Sf hSf hA5 F hA6 N V hV ν hν

/-- `theorem3_rotation_error_not_estimable` with the three background facts discharged. -/
theorem theorem3_rotation_error_not_estimable_unconditional
    (hk : 2 ≤ k) (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F) (j : Fin k) :
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
        thm1Limit n P.δ2 (lam P.GB F j) (sinSq ν (e j)) = t) :=
  theorem3_rotation_error_not_estimable fact1_slln (fact2_weyl n) (fact3_eigCont n) (fact2_weyl k) (fact3_eigCont k) hk P Sf hSf hA5 F hA6 j

/-- `corollary1_aggregate` with the three background facts discharged. -/
theorem corollary1_aggregate_unconditional
    (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F) {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (N : NoiseModel n P.var P.κ4 Ω μ) :
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
        (𝓝 (∑ j : Fin k, P.δ2 / ((n : ℝ) * lam P.GB F j + P.δ2))) :=
  corollary1_aggregate fact1_slln (fact2_weyl n) (fact3_eigCont n) (fact2_weyl k) (fact3_eigCont k) P Sf hSf hA5 F hA6 N

/-- `prop1_principal_coordinates` with the three background facts discharged. -/
theorem prop1_principal_coordinates_unconditional
    (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB) :
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
        Bmat P.Barr p * (CFC.sqrt Sf * Vpn P.Barr Sf p b * (Delta0Sqrt P.Barr Sf p)⁻¹) = b :=
  prop1_principal_coordinates (fact2_weyl k) P Sf hSf hA5

/-- `prop2_systematic_limits` with the three background facts discharged. -/
theorem prop2_systematic_limits_unconditional
    (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (V : Matrix (Fin k) (Fin k) ℝ) (hV : IsEigenbasis (Kmat Sf P.GB) V) :
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
      Tendsto (fun p : ℕ => Npn (b p) (Bmat P.Barr p) F) atTop (𝓝 (Nlim Sf P.GB V F)) :=
  prop2_systematic_limits (fact2_weyl k) P Sf hSf hA5 F V hV

/-- `prop3_observable_dual` with the three background facts discharged. -/
theorem prop3_observable_dual_unconditional
    (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB) (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F) {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (N : NoiseModel n P.var P.κ4 Ω μ) :
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
          Tendsto (fun p => |inner ℝ (wp p) w|) atTop (𝓝 1)) :=
  prop3_observable_dual fact1_slln (fact2_weyl n) P Sf hSf hA5 F hA6 N

/-- `cor3_large_n` with the three background facts discharged. -/
theorem cor3_large_n_unconditional
    (Sf GB V : Matrix (Fin k) (Fin k) ℝ) (hSf : Sf.PosDef) (hGB : GB.PosDef) (hA5 : Assumption5 Sf GB) (hV : IsEigenbasis (Kmat Sf GB) V) (f : ℕ → Fin k → ℝ) (hf : Tendsto (fun n : ℕ => (1 / (n : ℝ)) • (Fcols f n * (Fcols f n)ᵀ)) atTop (𝓝 Sf)) :
    Tendsto (fun n => Nlim Sf GB V (Fcols f n)) atTop (𝓝 (LamDiag Sf GB)) ∧
    (∀ j : Fin k, Tendsto (fun n => lam GB (Fcols f n) j) atTop
      (𝓝 (sortedEig (Kmat Sf GB) j))) ∧
    ∀ (j : Fin k) (ν : ℕ → EuclideanSpace ℝ (Fin k)),
      (∀ᶠ n in atTop, IsUnitEigvec (Nlim Sf GB V (Fcols f n)) (ν n)
        (sortedEig (Nlim Sf GB V (Fcols f n)) j)) →
      Tendsto (fun n => sinSq (ν n) (e j)) atTop (𝓝 0) :=
  cor3_large_n (fact2_weyl k) Sf GB V hSf hGB hA5 hV f hf

/-- `cor3_remark_independent_factors` with the three background facts discharged. -/
theorem cor3_remark_independent_factors_unconditional
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Sf : Matrix (Fin k) (Fin k) ℝ) (f : ℕ → Ω → Fin k → ℝ) (hmeas : ∀ l, Measurable (f l)) (hindep : iIndepFun f μ) (hmom : ∀ l a, MemLp (fun ω => f l ω a) 4 μ) (hcov : ∀ l a b, μ[fun ω => f l ω a * f l ω b] = Sf a b) (κf : ℝ) (h4 : ∀ l, μ[fun ω => (∑ a, f l ω a ^ 2) ^ 2] ≤ κf) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (1 / (n : ℝ)) •
      (Fcols (fun l => f l ω) n * (Fcols (fun l => f l ω) n)ᵀ)) atTop (𝓝 Sf) :=
  cor3_remark_independent_factors fact1_slln μ Sf f hmeas hindep hmom hcov κf h4

/-- `lemma2_i_eigenpair_convergence` with the three background facts discharged. -/
theorem lemma2_i_eigenpair_convergence_unconditional
    {m : ℕ} (A : ℕ → Matrix (Fin m) (Fin m) ℝ) (Ainf : Matrix (Fin m) (Fin m) ℝ) (hA : ∀ p, (A p).IsHermitian) (hAinf : Ainf.IsHermitian) (hlim : Tendsto A atTop (𝓝 Ainf)) (j : Fin m) (hsimple : ∀ i, i ≠ j → sortedEig Ainf i ≠ sortedEig Ainf j) (v : EuclideanSpace ℝ (Fin m)) (hv : IsUnitEigvec Ainf v (sortedEig Ainf j)) :
    (∀ᶠ p in atTop, ∀ i, i ≠ j → sortedEig (A p) i ≠ sortedEig (A p) j) ∧
    Tendsto (fun p => sortedEig (A p) j) atTop (𝓝 (sortedEig Ainf j)) ∧
    ∀ vp : ℕ → EuclideanSpace ℝ (Fin m),
      (∀ᶠ p in atTop, IsUnitEigvec (A p) (vp p) (sortedEig (A p) j)) →
      Tendsto (fun p => |inner ℝ (vp p) v|) atTop (𝓝 1) :=
  lemma2_i_eigenpair_convergence (fact2_weyl m) A Ainf hA hAinf hlim j hsimple v hv

end PCError

end
