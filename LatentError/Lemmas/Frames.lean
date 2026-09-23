import LatentError.Lemmas.Eigenbasis
import LatentError.Model

/-!
# Principal frames (Proposition 1 machinery)

With `A := B Σ_f^{1/2}` we have `A Aᵀ = Σ₀` and `Aᵀ A = p K⁽ᵖ⁾`, so Gram duality transports
the spectrum; for a principal frame `b` with positive eigenvalues `Δ₀`,
`V⁽ᵖ⁾ = Aᵀ b Δ₀^{-1/2}` is orthogonal and everything in Proposition 1 is matrix algebra.
-/

open scoped Matrix Topology MatrixOrder
open Filter

noncomputable section

namespace PCError

variable {k n : ℕ}

/-! ## Square roots and symmetry -/

lemma nonneg_of_posDef {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) : 0 ≤ S :=
  Matrix.nonneg_iff_posSemidef.2 hS.posSemidef

lemma transpose_eq_of_isHermitian {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.IsHermitian) :
    Sᵀ = S := by
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hS

lemma sqrt_transpose (S : Matrix (Fin k) (Fin k) ℝ) : (CFC.sqrt S)ᵀ = CFC.sqrt S :=
  transpose_eq_of_isHermitian (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg S)).isHermitian

lemma sqrt_mul_sqrt {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) :
    CFC.sqrt S * CFC.sqrt S = S :=
  CFC.sqrt_mul_sqrt_self S (nonneg_of_posDef hS)

lemma isHermitian_of_transpose_eq {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : Sᵀ = S) :
    S.IsHermitian := by
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hS

lemma kmat_transpose {S G : Matrix (Fin k) (Fin k) ℝ} (hG : Gᵀ = G) : (Kmat S G)ᵀ = Kmat S G := by
  simp [Kmat, Matrix.transpose_mul, sqrt_transpose, hG, Matrix.mul_assoc]

lemma kmat_isHermitian {S G : Matrix (Fin k) (Fin k) ℝ} (hG : Gᵀ = G) : (Kmat S G).IsHermitian :=
  isHermitian_of_transpose_eq (kmat_transpose hG)

lemma gBp_transpose (Barr : ℕ → Fin k → ℝ) (p : ℕ) : (GBp Barr p)ᵀ = GBp Barr p := by
  simp [GBp, Matrix.transpose_mul]

lemma kmat_isHermitian_of_assumption5 {S G : Matrix (Fin k) (Fin k) ℝ} (h5 : Assumption5 S G)
    (hk : 1 ≤ k) : (Kmat S G).IsHermitian := by
  by_contra h
  have := h5.2 ⟨0, hk⟩
  simp [sortedEig, h] at this

/-! ## Diagonal algebra -/

lemma diag_sqrt_mul_inv {x : Fin k → ℝ} (hx : ∀ j, 0 < x j) :
    Matrix.diagonal (fun j => Real.sqrt (x j)) * Matrix.diagonal (fun j => 1 / Real.sqrt (x j)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j
  have := Real.sqrt_pos.2 (hx j)
  field_simp

lemma diag_inv_mul_sqrt {x : Fin k → ℝ} (hx : ∀ j, 0 < x j) :
    Matrix.diagonal (fun j => 1 / Real.sqrt (x j)) * Matrix.diagonal (fun j => Real.sqrt (x j)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j
  have := Real.sqrt_pos.2 (hx j)
  field_simp

lemma diag_mul_inv_sqrt {x : Fin k → ℝ} (hx : ∀ j, 0 < x j) :
    Matrix.diagonal x * Matrix.diagonal (fun j => 1 / Real.sqrt (x j)) =
      Matrix.diagonal (fun j => Real.sqrt (x j)) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext j
  have h := Real.sqrt_pos.2 (hx j)
  have := Real.mul_self_sqrt (hx j).le
  field_simp
  linarith

lemma diag_inv_sqrt_mul_mul {x : Fin k → ℝ} (hx : ∀ j, 0 < x j) :
    Matrix.diagonal (fun j => 1 / Real.sqrt (x j)) * Matrix.diagonal x *
      Matrix.diagonal (fun j => 1 / Real.sqrt (x j)) = 1 := by
  rw [Matrix.mul_assoc, diag_mul_inv_sqrt hx, diag_inv_mul_sqrt hx]

lemma diag_sqrt_mul_self {x : Fin k → ℝ} (hx : ∀ j, 0 ≤ x j) :
    Matrix.diagonal (fun j => Real.sqrt (x j)) * Matrix.diagonal (fun j => Real.sqrt (x j)) =
      Matrix.diagonal x := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext j
  exact Real.mul_self_sqrt (hx j)

lemma diag_sqrt_inv {x : Fin k → ℝ} (hx : ∀ j, 0 < x j) :
    (Matrix.diagonal (fun j => Real.sqrt (x j)))⁻¹ =
      Matrix.diagonal (fun j => 1 / Real.sqrt (x j)) :=
  Matrix.inv_eq_right_inv (diag_sqrt_mul_inv hx)

/-! ## Principal frames in matrix form -/

lemma IsPrincipalFrame.mul_eq {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    {b : Matrix (Fin p) (Fin k) ℝ} (hb : IsPrincipalFrame S b) :
    S * b = b * Matrix.diagonal (fun j : Fin k => sortedEigN S j) := by
  refine ext_colVec fun j => ?_
  rw [colVec_mul, colVec_mul_diagonal, hb.2 j]

lemma isPrincipalFrame_of_mul_eq {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    {b : Matrix (Fin p) (Fin k) ℝ} (hb : bᵀ * b = 1)
    (h : S * b = b * Matrix.diagonal (fun j : Fin k => sortedEigN S j)) :
    IsPrincipalFrame S b :=
  ⟨hb, fun j => by rw [← colVec_mul, h, colVec_mul_diagonal]⟩

/-! ## The factor `A = B Σ_f^{1/2}` -/

/-- `A = B Σ_f^{1/2}`. -/
def Afac (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) :
    Matrix (Fin p) (Fin k) ℝ :=
  Bmat Barr p * CFC.sqrt Sf

lemma afac_transpose (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) :
    (Afac Barr Sf p)ᵀ = CFC.sqrt Sf * (Bmat Barr p)ᵀ := by
  simp [Afac, Matrix.transpose_mul, sqrt_transpose]

lemma afac_mul_transpose (Barr : ℕ → Fin k → ℝ) {Sf : Matrix (Fin k) (Fin k) ℝ}
    (hSf : Sf.PosDef) (p : ℕ) : Afac Barr Sf p * (Afac Barr Sf p)ᵀ = Sig0 Barr Sf p := by
  rw [afac_transpose, Afac, Sig0, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt Sf),
    sqrt_mul_sqrt hSf, Matrix.mul_assoc]

lemma afac_transpose_mul (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) {p : ℕ}
    (hp : p ≠ 0) : (Afac Barr Sf p)ᵀ * Afac Barr Sf p = (p : ℝ) • Kmat Sf (GBp Barr p) := by
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [afac_transpose, Afac, Kmat, GBp, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    mul_one_div_cancel hp', one_smul]
  simp only [Matrix.mul_assoc]

lemma sortedEigN_sig0 (Barr : ℕ → Fin k → ℝ) {Sf : Matrix (Fin k) (Fin k) ℝ} (hSf : Sf.PosDef)
    {p : ℕ} (hp : p ≠ 0) (i : ℕ) :
    sortedEigN (Sig0 Barr Sf p) i = (p : ℝ) * sortedEigN (Kmat Sf (GBp Barr p)) i := by
  rw [← afac_mul_transpose Barr hSf p, sortedEigN_mul_transpose, afac_transpose_mul Barr Sf hp,
    sortedEigN_smul (kmat_isHermitian (gBp_transpose Barr p)) (Nat.cast_nonneg p)]

/-! ## Frames from eigenbases and eigenbases from frames -/

/-- The eigenvalues `p μⱼ⁽ᵖ⁾` as a function on `Fin k`. -/
def pmu (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) : Fin k → ℝ :=
  fun j => (p : ℝ) * sortedEig (Kmat Sf (GBp Barr p)) j

lemma diag_sortedEigN_sig0 (Barr : ℕ → Fin k → ℝ) {Sf : Matrix (Fin k) (Fin k) ℝ}
    (hSf : Sf.PosDef) {p : ℕ} (hp : p ≠ 0) :
    Matrix.diagonal (fun j : Fin k => sortedEigN (Sig0 Barr Sf p) j) =
      Matrix.diagonal (pmu Barr Sf p) := by
  congr 1; funext j
  rw [sortedEigN_sig0 Barr hSf hp, pmu, sortedEigN, dif_pos j.2]

lemma vpn_eq (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ)
    (b : Matrix (Fin p) (Fin k) ℝ) :
    Vpn Barr Sf p b =
      (Afac Barr Sf p)ᵀ * b * Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j)) := by
  rw [afac_transpose]; rfl

lemma delta0Sqrt_eq (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) :
    Delta0Sqrt Barr Sf p = Matrix.diagonal (fun j => Real.sqrt (pmu Barr Sf p j)) := rfl

/-- The matrix algebra behind Proposition 1, with all matrices abstract. -/
lemma frame_algebra {p : ℕ} {A b : Matrix (Fin p) (Fin k) ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    {K D' D0 Δ Ds : Matrix (Fin k) (Fin k) ℝ} {c : ℝ} (hc : c ≠ 0)
    (hAA : A * Aᵀ = S) (hAtA : Aᵀ * A = c • K) (hb : bᵀ * b = 1) (hSb : S * b = b * Δ)
    (h1 : D' * Δ * D' = 1) (h2 : Δ * D' = D0) (h4 : D' * D0 = 1)
    (h5 : D0 * D0ᵀ = Δ) (h6 : D'ᵀ = D') (h7 : D' * Δ = Δ * D') (h8 : Δ = c • Ds) :
    (Aᵀ * b * D')ᵀ * (Aᵀ * b * D') = 1 ∧ A * (Aᵀ * b * D') = b * D0 ∧ b * Δ * bᵀ = S ∧
      Aᵀ * b = (Aᵀ * b * D') * D0 ∧ K * (Aᵀ * b * D') = (Aᵀ * b * D') * Ds := by
  have hbSb : bᵀ * S * b = Δ := by
    rw [Matrix.mul_assoc, hSb, ← Matrix.mul_assoc, hb, Matrix.one_mul]
  have hVV : (Aᵀ * b * D')ᵀ * (Aᵀ * b * D') = 1 := by
    calc (Aᵀ * b * D')ᵀ * (Aᵀ * b * D') = D' * (bᵀ * (A * Aᵀ) * b) * D' := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, h6, Matrix.mul_assoc]
      _ = 1 := by rw [hAA, hbSb, h1]
  have hAV : A * (Aᵀ * b * D') = b * D0 := by
    calc A * (Aᵀ * b * D') = (A * Aᵀ) * b * D' := by simp only [Matrix.mul_assoc]
      _ = b * (Δ * D') := by rw [hAA, hSb, Matrix.mul_assoc]
      _ = b * D0 := by rw [h2]
  have hVVt : (Aᵀ * b * D') * (Aᵀ * b * D')ᵀ = 1 := mul_eq_one_comm.1 hVV
  refine ⟨hVV, hAV, ?_, ?_, ?_⟩
  · calc b * Δ * bᵀ = (b * D0) * (b * D0)ᵀ := by
          rw [← h5]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = A * ((Aᵀ * b * D') * (Aᵀ * b * D')ᵀ) * Aᵀ := by
          rw [← hAV]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
            Matrix.mul_assoc]
      _ = S := by rw [hVVt, Matrix.mul_one, hAA]
  · calc Aᵀ * b = Aᵀ * b * (D' * D0) := by rw [h4, Matrix.mul_one]
      _ = (Aᵀ * b * D') * D0 := by simp only [Matrix.mul_assoc]
  · have key : c • (K * (Aᵀ * b * D')) = c • ((Aᵀ * b * D') * Ds) := by
      calc c • (K * (Aᵀ * b * D')) = (Aᵀ * A) * (Aᵀ * b * D') := by
            rw [hAtA, Matrix.smul_mul]
        _ = Aᵀ * (S * b) * D' := by rw [← hAA]; simp only [Matrix.mul_assoc]
        _ = Aᵀ * b * (Δ * D') := by rw [hSb]; simp only [Matrix.mul_assoc]
        _ = (Aᵀ * b * D') * Δ := by rw [← h7]; simp only [Matrix.mul_assoc]
        _ = c • ((Aᵀ * b * D') * Ds) := by rw [h8, Matrix.mul_smul]
    exact smul_right_injective _ hc key

section frame

variable {Barr : ℕ → Fin k → ℝ} {Sf : Matrix (Fin k) (Fin k) ℝ} {p : ℕ}
  {b : Matrix (Fin p) (Fin k) ℝ}

/-- Diagonal facts for `D' = Δ₀^{-1/2}`, `D0 = Δ₀^{1/2}`, `Δ = Δ₀ = p diag μ⁽ᵖ⁾`. -/
lemma frame_diag (hpos : ∀ j, 0 < pmu Barr Sf p j) :
    let D' := Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j))
    let Δ := Matrix.diagonal (pmu Barr Sf p)
    let D0 := Delta0Sqrt Barr Sf p
    D' * Δ * D' = 1 ∧ Δ * D' = D0 ∧ D' * D0 = 1 ∧ D0 * D0ᵀ = Δ ∧ D'ᵀ = D' ∧
      D' * Δ = Δ * D' ∧
      Δ = (p : ℝ) • Matrix.diagonal (sortedEig (Kmat Sf (GBp Barr p))) := by
  intro D' Δ D0
  refine ⟨diag_inv_sqrt_mul_mul hpos, diag_mul_inv_sqrt hpos, diag_inv_mul_sqrt hpos, ?_,
    Matrix.diagonal_transpose _, ?_, ?_⟩
  · simp only [D0, delta0Sqrt_eq, Matrix.diagonal_transpose]
    exact diag_sqrt_mul_self fun j => (hpos j).le
  · simp only [D', Δ, Matrix.diagonal_mul_diagonal, mul_comm]
  · rw [← Matrix.diagonal_smul]; rfl

/-- Everything Proposition 1 says about a principal frame, assuming positive `μ⁽ᵖ⁾`. -/
theorem frame_facts (hSf : Sf.PosDef) (hp : p ≠ 0) (hpos : ∀ j, 0 < pmu Barr Sf p j)
    (hb : IsPrincipalFrame (Sig0 Barr Sf p) b) :
    (Vpn Barr Sf p b)ᵀ * Vpn Barr Sf p b = 1 ∧
    Afac Barr Sf p * Vpn Barr Sf p b = b * Delta0Sqrt Barr Sf p ∧
    b * Matrix.diagonal (fun j : Fin k => sortedEigN (Sig0 Barr Sf p) j) * bᵀ = Sig0 Barr Sf p ∧
    CFC.sqrt Sf * (Bmat Barr p)ᵀ * b = Vpn Barr Sf p b * Delta0Sqrt Barr Sf p ∧
    IsEigenbasis (Kmat Sf (GBp Barr p)) (Vpn Barr Sf p b) := by
  obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ := frame_diag (Barr := Barr) (Sf := Sf) hpos
  have hSb := hb.mul_eq
  rw [diag_sortedEigN_sig0 Barr hSf hp] at hSb
  obtain ⟨e1, e2, e3, e4, e5⟩ := frame_algebra (Nat.cast_ne_zero.2 hp)
    (afac_mul_transpose Barr hSf p) (afac_transpose_mul Barr Sf hp) hb.1 hSb h1 h2 h4 h5 h6 h7 h8
  rw [vpn_eq, diag_sortedEigN_sig0 Barr hSf hp, ← afac_transpose]
  exact ⟨e1, e2, e3, e4, e1, e5⟩

lemma frame_C (hSf : Sf.PosDef) (hp : p ≠ 0) (hpos : ∀ j, 0 < pmu Barr Sf p j)
    (hb : IsPrincipalFrame (Sig0 Barr Sf p) b) :
    Bmat Barr p * (CFC.sqrt Sf * Vpn Barr Sf p b * (Delta0Sqrt Barr Sf p)⁻¹) = b := by
  have hAV := (frame_facts hSf hp hpos hb).2.1
  rw [delta0Sqrt_eq, diag_sqrt_inv hpos, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change Afac Barr Sf p * Vpn Barr Sf p b * _ = b
  rw [hAV, delta0Sqrt_eq, Matrix.mul_assoc, diag_sqrt_mul_inv hpos, Matrix.mul_one]

lemma frame_V_unique (hSf : Sf.PosDef) (hp : p ≠ 0) (hpos : ∀ j, 0 < pmu Barr Sf p j)
    (hb : IsPrincipalFrame (Sig0 Barr Sf p) b) (V : Matrix (Fin k) (Fin k) ℝ) :
    (Vᵀ * V = 1 ∧ CFC.sqrt Sf * (Bmat Barr p)ᵀ * b = V * Delta0Sqrt Barr Sf p) ↔
      V = Vpn Barr Sf p b := by
  have hf := frame_facts hSf hp hpos hb
  constructor
  · rintro ⟨-, hV⟩
    rw [vpn_eq, afac_transpose, hV, delta0Sqrt_eq, Matrix.mul_assoc, diag_sqrt_mul_inv hpos,
      Matrix.mul_one]
  · rintro rfl
    exact ⟨hf.1, hf.2.2.2.1⟩

/-- A principal frame exists once `μ⁽ᵖ⁾ > 0`. -/
lemma exists_frame (hSf : Sf.PosDef) (hp : p ≠ 0) (hpos : ∀ j, 0 < pmu Barr Sf p j) :
    ∃ b : Matrix (Fin p) (Fin k) ℝ, IsPrincipalFrame (Sig0 Barr Sf p) b := by
  obtain ⟨U, hU⟩ := exists_isEigenbasis (kmat_isHermitian (gBp_transpose Barr p))
  obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ := frame_diag (Barr := Barr) (Sf := Sf) hpos
  have hKU : (Afac Barr Sf p)ᵀ * Afac Barr Sf p * U =
      U * Matrix.diagonal (pmu Barr Sf p) := by
    rw [afac_transpose_mul Barr Sf hp, Matrix.smul_mul, hU.2, h8, Matrix.mul_smul]
  refine ⟨Afac Barr Sf p * U * Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j)),
    isPrincipalFrame_of_mul_eq ?_ ?_⟩
  · calc (Afac Barr Sf p * U * Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j)))ᵀ *
          (Afac Barr Sf p * U * Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j)))
        = Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j)) *
            (Uᵀ * ((Afac Barr Sf p)ᵀ * Afac Barr Sf p * U)) *
            Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j)) := by
          simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [hKU, ← Matrix.mul_assoc Uᵀ, hU.1, Matrix.one_mul, h1]
  · rw [diag_sortedEigN_sig0 Barr hSf hp, ← afac_mul_transpose Barr hSf p]
    calc Afac Barr Sf p * (Afac Barr Sf p)ᵀ *
          (Afac Barr Sf p * U * Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j)))
        = Afac Barr Sf p * ((Afac Barr Sf p)ᵀ * Afac Barr Sf p * U) *
            Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j)) := by
          simp only [Matrix.mul_assoc]
      _ = Afac Barr Sf p * U * (Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j)) *
            Matrix.diagonal (pmu Barr Sf p)) := by
          rw [hKU, h7]; simp only [Matrix.mul_assoc]
      _ = Afac Barr Sf p * U * Matrix.diagonal (fun j => 1 / Real.sqrt (pmu Barr Sf p j)) *
            Matrix.diagonal (pmu Barr Sf p) := by simp only [Matrix.mul_assoc]

end frame

end PCError

end
