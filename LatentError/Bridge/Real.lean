import LatentError.Bridge.Glue
import LatentError.Lemmas.HardLeaves
import LatentError.Ono.Solution

/-!
# Bridge to Ono's `AsymptoticModel`: the real data

On the almost-sure event of Proposition 3, the paper's data give an instance of Ono's
`AsymptoticModel` (`LatentError/Ono/Solution.lean`):
* for large `p`: the loadings, a fixed sign-normalized sequence of principal frames `b★`,
  the noise path, the given sample eigenvectors `h`, and sign-pinned dual eigenvectors;
* for the finitely many small `p`: the filler data `glue`.

Ono's proved theorems then apply to this instance.  `Main.lean` transfers their conclusions
to arbitrary principal frames and eigenvector choices.

* `modelOfPerP`: assemble the model from per-`p` data and the limit facts.
* `realPerP`: the per-`p` fields for the real data at one large `p`.
* `exists_model`: the model built from the real data along one noise path.
-/

open scoped Matrix Topology MatrixOrder
open Filter MeasureTheory

noncomputable section

namespace PCError

variable {k n : ℕ}

/-! ## Assembling Ono's model -/

lemma posDef_of_sortedEig_pos {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian)
    (h : ∀ j, 0 < sortedEig A j) : A.PosDef := by
  refine hA.posDef_iff_eigenvalues_pos.2 fun i => ?_
  obtain ⟨e, he⟩ := sortedEig_eq_eigenvalues_comp hA
  have := h (e.symm i)
  rw [he] at this
  simpa using this

lemma eigenvalues_injective_of_strictAnti {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (h : StrictAnti (sortedEig A)) : Function.Injective hA.eigenvalues := by
  obtain ⟨e, he⟩ := sortedEig_eq_eigenvalues_comp hA
  intro a b hab
  have h1 : sortedEig A (e.symm a) = sortedEig A (e.symm b) := by simp [he, hab]
  simpa using h.injective h1

/-- The `p`-free data of Ono's model. -/
structure LimitData (k n : ℕ) (F : Matrix (Fin k) (Fin n) ℝ) (GB : Matrix (Fin k) (Fin k) ℝ) where
  Φbarinf : Matrix (Fin k) (Fin n) ℝ
  lam : Fin k → ℝ
  wn : Fin k → EuclideanSpace ℝ (Fin n)
  νn : Fin k → EuclideanSpace ℝ (Fin k)
  hlam_pos : ∀ j, 0 < lam j
  hlam_sorted : StrictAnti lam
  hwn_unit : ∀ j, ‖wn j‖ = 1
  hνn_unit : ∀ j, ‖νn j‖ = 1
  hwn_eig : ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / (n : ℝ)) • (Fᵀ * GB * F)) (wn j) = lam j • wn j
  hνn_eig : ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / (n : ℝ)) • (Φbarinf * Φbarinfᵀ)) (νn j) = lam j • νn j
  duality : ∀ j : Fin k,
    Matrix.toEuclideanLin Φbarinf (wn j) = Real.sqrt (n * lam j) • νn j

/-- Ono's `AsymptoticModel` from per-`p` data `D` and the limit facts about it. -/
def modelOfPerP {δ2 : ℝ} (hk : 1 ≤ k) (hkn : k < n) (hδ : 0 < δ2)
    {F : Matrix (Fin k) (Fin n) ℝ} {Sf GB : Matrix (Fin k) (Fin k) ℝ}
    (hSf : Sf.PosDef) (hGB : GB.PosDef) (hA5 : Assumption5 Sf GB)
    (D : (P : Adm k) → PerP k n hkn F Sf P.1) (L : LimitData k n F GB)
    (f1 : Tendsto (fun P : Adm k => (1 / ((n : ℝ) * P.1)) • ((D P).Zᵀ * (D P).Z)) atTop
      (𝓝 ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ))))
    (f2 : Tendsto (fun P : Adm k => (1 / Real.sqrt P.1) • ((D P).bᵀ * (D P).Z)) atTop
      (𝓝 (0 : Matrix (Fin k) (Fin n) ℝ)))
    (f3 : Tendsto (fun P : Adm k => (1 / Real.sqrt P.1) • (D P).Φ) atTop (𝓝 L.Φbarinf))
    (f4a : ∀ j : Fin k, Tendsto (fun P : Adm k => (D P).θ (Fin.castLE (le_of_lt hkn) j)) atTop
      (𝓝 (L.lam j + δ2 / n)))
    (f4b : Tendsto (fun P : Adm k => (1 / ((n : ℝ) - k)) *
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), (D P).θ i) atTop
      (𝓝 (δ2 / n)))
    (f5 : ∀ j : Fin k, Tendsto (fun P : Adm k => (D P).w j) atTop (𝓝 (L.wn j)))
    (f6 : ∀ j : Fin k, Tendsto (fun P : Adm k => (D P).ν j) atTop (𝓝 (L.νn j)))
    (f7 : Tendsto (fun P : Adm k => (1 / (P.1 : ℝ)) • ((D P).Bᵀ * (D P).B)) atTop (𝓝 GB)) :
    AsymptoticModel k n δ2 where
  hk := hk
  hkn := hkn
  hδ2 := hδ
  B P := (D P).B
  Sf := Sf
  b P := (D P).b
  F := F
  Φ P := (D P).Φ
  Z P := (D P).Z
  h P := (D P).h
  w P := (D P).w
  ν P := (D P).ν
  θ P := (D P).θ
  νval P := (D P).νval
  Φbarinf := L.Φbarinf
  GB := GB
  lam := L.lam
  wn := L.wn
  νn := L.νn
  hb_ortho P := (D P).hb_ortho
  hB_rank P := (D P).hB_rank
  hcol_eq P := (D P).hcol_eq
  hBF P := (D P).hBF
  hSf := hSf
  hGB := hGB
  SfSqrt := CFC.sqrt Sf
  hSfSqrt_psd := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Sf)
  hSfSqrt_sq := sqrt_mul_sqrt hSf
  hSfGB_herm := kmat_isHermitian (transpose_eq_of_isHermitian hGB.isHermitian)
  hSfGB_posDef := posDef_of_sortedEig_pos
    (kmat_isHermitian (transpose_eq_of_isHermitian hGB.isHermitian)) hA5.2
  hSfGB_distinct := eigenvalues_injective_of_strictAnti
    (kmat_isHermitian (transpose_eq_of_isHermitian hGB.isHermitian)) hA5.1
  sig0 P := (D P).sig0
  hsig0_pos P := (D P).hsig0_pos
  hsig0_sorted P := (D P).hsig0_sorted
  hb_eig P := (D P).hb_eig
  hθ_sorted P := (D P).hθ_sorted
  hθ_spectrum P := (D P).hθ_spectrum
  hh_unit P := (D P).hh_unit
  hH_ortho P := (D P).hH_ortho
  hh_eig P := (D P).hh_eig
  hw_unit P := (D P).hw_unit
  hw_eig P := (D P).hw_eig
  hν_unit P := (D P).hν_unit
  hνval_sorted P := (D P).hνval_sorted
  hν_eig P := (D P).hν_eig
  hlam_pos := L.hlam_pos
  hlam_sorted := L.hlam_sorted
  hwn_unit := L.hwn_unit
  hνn_unit := L.hνn_unit
  hwn_eig := L.hwn_eig
  hνn_eig := L.hνn_eig
  field1_noiseGram := f1
  field2_decoherence := f2
  field3_signalLimit := f3
  field4_dualSpectrum := f4a
  field4_trailing := f4b
  field5_dualEigvec := f5
  field6_duality := L.duality
  field6_nuLimit := f6
  field7_BtB := f7

/-! ## Small tools -/

/-- `1` or `-1` by the sign of `x` (`1` at `0`). -/
def sgn1 (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma sgn1_pm (x : ℝ) : sgn1 x = 1 ∨ sgn1 x = -1 := by
  unfold sgn1; split_ifs <;> simp

lemma sgn1_eq_sign {x : ℝ} (hx : x ≠ 0) : sgn1 x = Real.sign x := by
  unfold sgn1
  rcases lt_or_gt_of_ne hx with h | h
  · rw [if_neg (not_le.2 h), Real.sign_of_neg h]
  · rw [if_pos h.le, Real.sign_of_pos h]

/-- Sign pinning with a sign that is `±1` at every `p`. -/
lemma tendsto_sgn1_smul {m : ℕ} {u : ℕ → EuclideanSpace ℝ (Fin m)}
    {u0 : EuclideanSpace ℝ (Fin m)} (hu : ∀ p, ‖u p‖ = 1) (hu0 : ‖u0‖ = 1)
    (h : Tendsto (fun p => |inner ℝ (u p) u0|) atTop (𝓝 1)) :
    Tendsto (fun p => sgn1 (inner ℝ (u p) u0) • u p) atTop (𝓝 u0) := by
  obtain ⟨hne, hlim⟩ := sign_pinning u u0 hu hu0 h
  refine hlim.congr' ?_
  filter_upwards [hne] with p hp
  rw [sgn1_eq_sign hp]

/-- A limit along `ℕ` gives the limit along `Adm k` of a family that agrees with it for
large `p`. -/
lemma tendsto_adm_of_eq {X : Type*} {g : Adm k → X} {f : ℕ → X} {l : Filter X} (p0 : ℕ)
    (hgf : ∀ Q : Adm k, p0 ≤ Q.1 → g Q = f Q.1) (hf : Tendsto f atTop l) :
    Tendsto g atTop l := by
  refine ((tendsto_adm_iff (k := k)).2 hf).congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨⟨max p0 k, le_max_right _ _⟩, fun Q hQ => (hgf Q ?_).symm⟩
  exact le_trans (le_max_left _ _) (show max p0 k ≤ Q.1 from hQ)

lemma card_filter_fin_ge (k n : ℕ) :
    (Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ))).card = n - k := by
  have : (Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ))).map Fin.valEmbedding =
      Finset.Ico k n := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, a.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Ico]

lemma scov_transpose (Barr : ℕ → Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (Zarr : ℕ → Fin n → ℝ) (p : ℕ) : (Scov Barr F Zarr p)ᵀ = Scov Barr F Zarr p := by
  simp [Scov, Matrix.transpose_mul]

lemma sortedEigN_scov (Barr : ℕ → Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (Zarr : ℕ → Fin n → ℝ) (p : ℕ) (i : ℕ) :
    sortedEigN (Scov Barr F Zarr p) i = theta Barr F Zarr p i :=
  congrFun (sortedEigN_gram_swap (Ymat Barr F Zarr p) (c := 1 / ((n : ℝ) * p))
    (by positivity)) i

lemma theta_eq_sortedEig (Barr : ℕ → Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (Zarr : ℕ → Fin n → ℝ) (p : ℕ) (hkn : k < n) (j : Fin k) :
    theta Barr F Zarr p j = sortedEig (Wdual Barr F Zarr p) (Fin.castLE hkn.le j) :=
  sortedEigN_eq_fin _ _ _

/-! ## Proposition 3(b) along a fixed frame sequence, as a matrix limit -/

theorem NoiseModel.frame_noise_limit {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {var : ℕ → Fin n → ℝ} {κ4 : ℝ} (N : NoiseModel n var κ4 Ω μ)
    (b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ) (hb : ∀ᶠ p in atTop, (b p)ᵀ * b p = 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ =>
      (1 / Real.sqrt p) • ((b p)ᵀ * truncRows (N.path ω) p)) atTop (𝓝 0) := by
  have hu : ∀ j : Fin k, ∀ᶠ p in atTop, ‖colVec (b p) j‖ = 1 := fun j =>
    hb.mono fun p hp => norm_colVec (b p) hp j
  have h : ∀ᵐ ω ∂μ, ∀ j l, Tendsto (fun p : ℕ =>
      (∑ i : Fin p, colVec (b p) j i * N.Z i l ω) / Real.sqrt p) atTop (𝓝 0) :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun l =>
      N.concentration (fun p => colVec (b p) j) (hu j) l
  filter_upwards [h] with ω hω
  refine tendsto_matrix_of_entries fun j l => ?_
  refine (hω j l).congr fun p => ?_
  rw [Matrix.smul_apply, transpose_mul_truncRows_apply, smul_eq_mul, div_eq_inv_mul, one_div]
  try rfl

/-! ## The real data at one large `p` -/

/-- Facts that hold at every large `p` along a good noise path. -/
structure RealFacts (P : LoadingParams k n) (Sf : Matrix (Fin k) (Fin k) ℝ)
    (F : Matrix (Fin k) (Fin n) ℝ) (Zarr : ℕ → Fin n → ℝ) (p : ℕ)
    (b : Matrix (Fin p) (Fin k) ℝ) (h : Fin k → EuclideanSpace ℝ (Fin p)) : Prop where
  hkp : k ≤ p
  hp : p ≠ 0
  hpos : ∀ j, 0 < pmu P.Barr Sf p j
  hK : StrictAnti (sortedEig (Kmat Sf (GBp P.Barr p)))
  hb : IsPrincipalFrame (Sig0 P.Barr Sf p) b
  hdet : IsUnit ((Bmat P.Barr p)ᵀ * Bmat P.Barr p).det
  hh : ∀ j : Fin k, IsUnitEigvec (Scov P.Barr F Zarr p) (h j)
    (sortedEigN (Scov P.Barr F Zarr p) j)
  hH : (Hmat h)ᵀ * Hmat h = 1

namespace RealFacts

variable {P : LoadingParams k n} {Sf : Matrix (Fin k) (Fin k) ℝ}
  {F : Matrix (Fin k) (Fin n) ℝ} {Zarr : ℕ → Fin n → ℝ} {p : ℕ}
  {b : Matrix (Fin p) (Fin k) ℝ} {h : Fin k → EuclideanSpace ℝ (Fin p)}

lemma proj (R : RealFacts P Sf F Zarr p b h) (hSf : Sf.PosDef) :
    b * bᵀ * Bmat P.Barr p = Bmat P.Barr p :=
  frame_proj_B hSf R.hp R.hpos R.hb

lemma BF (R : RealFacts P Sf F Zarr p b h) (hSf : Sf.PosDef) :
    Bmat P.Barr p * F = b * PhiMat b (Bmat P.Barr p) F := by
  rw [PhiMat, ← Matrix.mul_assoc, ← Matrix.mul_assoc, R.proj hSf]

lemma Y (R : RealFacts P Sf F Zarr p b h) (hSf : Sf.PosDef) :
    b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p = Ymat P.Barr F Zarr p := by
  rw [← R.BF hSf]; rfl

lemma wdual_eq (R : RealFacts P Sf F Zarr p b h) (hSf : Sf.PosDef) :
    (1 / ((n : ℝ) * p)) • ((b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p)ᵀ *
      (b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p)) = Wdual P.Barr F Zarr p := by
  rw [R.Y hSf]; rfl

lemma scov_eq (R : RealFacts P Sf F Zarr p b h) (hSf : Sf.PosDef) :
    Scov P.Barr F Zarr p = (1 / ((n : ℝ) * p)) •
      ((b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p) *
        (b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p)ᵀ) := by
  rw [R.Y hSf]; rfl

lemma pmu_strictAnti (R : RealFacts P Sf F Zarr p b h) : StrictAnti (pmu P.Barr Sf p) := by
  intro i j hij
  have hp' : (0 : ℝ) < p := Nat.cast_pos.2 (Nat.pos_of_ne_zero R.hp)
  exact mul_lt_mul_of_pos_left (R.hK hij) hp'

lemma hb_eig (R : RealFacts P Sf F Zarr p b h) (hSf : Sf.PosDef) (j : Fin k) :
    Matrix.toEuclideanLin (Bmat P.Barr p * Sf * (Bmat P.Barr p)ᵀ) (colVec b j) =
      pmu P.Barr Sf p j • colVec b j := by
  have h1 := R.hb.2 j
  have h2 : sortedEigN (Sig0 P.Barr Sf p) j = pmu P.Barr Sf p j := by
    rw [sortedEigN_sig0 P.Barr hSf R.hp, sortedEigN_eq_fin _ _ j.2]
    rfl
  rw [h2] at h1
  exact h1

lemma hh_eig (R : RealFacts P Sf F Zarr p b h) (hSf : Sf.PosDef) (j : Fin k) :
    Matrix.toEuclideanLin ((1 / ((n : ℝ) * p)) •
        ((b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p) *
          (b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p)ᵀ)) (h j) =
      sortedEig ((1 / ((n : ℝ) * p)) •
        ((b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p)ᵀ *
          (b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p)))
        (Fin.castLE P.hkn.le j) • h j := by
  have e2 : sortedEigN (Scov P.Barr F Zarr p) j = sortedEig ((1 / ((n : ℝ) * p)) •
      ((b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p)ᵀ *
        (b * PhiMat b (Bmat P.Barr p) F + truncRows Zarr p))) (Fin.castLE P.hkn.le j) := by
    rw [R.scov_eq hSf, sortedEigN_eq_fin _ _ (lt_of_lt_of_le j.2 R.hkp)]
    exact sortedEig_S_eq_W R.hkp P.hkn _ (by positivity) j
  have := (R.hh j).2
  rw [e2, R.scov_eq hSf] at this
  exact this

end RealFacts

/-- Ono's per-`p` fields for the real data at one large `p`. -/
def realPerP (P : LoadingParams k n) {Sf : Matrix (Fin k) (Fin k) ℝ} (hSf : Sf.PosDef)
    (F : Matrix (Fin k) (Fin n) ℝ) (Zarr : ℕ → Fin n → ℝ) {p : ℕ}
    {b : Matrix (Fin p) (Fin k) ℝ} {h : Fin k → EuclideanSpace ℝ (Fin p)}
    (R : RealFacts P Sf F Zarr p b h) (sw sν : Fin k → ℝ)
    (hsw : ∀ j, sw j = 1 ∨ sw j = -1) (hsν : ∀ j, sν j = 1 ∨ sν j = -1) :
    PerP k n P.hkn F Sf p :=
  PerP.ofFrame R.hkp P.hkn F Sf (Bmat P.Barr p) b (PhiMat b (Bmat P.Barr p) F)
    (truncRows Zarr p) (pmu P.Barr Sf p) h sw sν R.hb.1
    (rank_eq_of_transpose_mul_isUnit R.hdet)
    (range_eq_of_factor (M := bᵀ * Bmat P.Barr p)
      (by rw [← Matrix.mul_assoc, R.proj hSf]) (frame_C hSf R.hp R.hpos R.hb).symm)
    (R.BF hSf) R.hpos R.pmu_strictAnti (R.hb_eig hSf) (fun j => (R.hh j).1) R.hH
    (R.hh_eig hSf) hsw hsν

/-! ## The limit data -/

lemma exists_w0_eigvec {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GB.PosDef) (hkn : k < n)
    (F : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) :
    ∃ w, IsUnitEigvec (W0 GB F) w (lam GB F j) := by
  have hs := transpose_eq_of_isHermitian hGB.isHermitian
  obtain ⟨w, hw⟩ := exists_unitEigvec_sortedEig (w0_isHermitian hs F) ⟨j, lt_trans j.2 hkn⟩
  refine ⟨w, ?_⟩
  rwa [lam, sortedEigN_eq_fin _ _ (lt_trans j.2 hkn)]

section limit

variable (P : LoadingParams k n) {Sf V : Matrix (Fin k) (Fin k) ℝ} (hSf : Sf.PosDef)
  (hA5 : Assumption5 Sf P.GB) (hV : IsEigenbasis (Kmat Sf P.GB) V)
  (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F)

/-- `wⱼ`: a chosen unit eigenvector of `W₀` at `λⱼ`. -/
def wChoice (j : Fin k) : EuclideanSpace ℝ (Fin n) :=
  Classical.choose (exists_w0_eigvec P.GB_posDef P.hkn F j)

lemma wChoice_spec (j : Fin k) : IsUnitEigvec (W0 P.GB F) (wChoice P F j) (lam P.GB F j) :=
  Classical.choose_spec (exists_w0_eigvec P.GB_posDef P.hkn F j)

/-- `νⱼ := Φ̄^∞ wⱼ / √(nλⱼ)` (Corollary 2). -/
def nuChoice (j : Fin k) : EuclideanSpace ℝ (Fin k) :=
  (1 / Real.sqrt ((n : ℝ) * lam P.GB F j)) •
    Matrix.toEuclideanLin (PhiBarInf Sf P.GB V F) (wChoice P F j)

include hSf hA5 hV hA6 in
lemma nuChoice_spec (j : Fin k) :
    IsUnitEigvec (Nlim Sf P.GB V F) (nuChoice P (Sf := Sf) (V := V) F j) (lam P.GB F j) :=
  nlim_eigvec_of_w0 hSf hA5 hV F (hA6.2 j) (wChoice_spec P F j)

/-- The limit data of the real model. -/
def limitData : LimitData k n F P.GB where
  Φbarinf := PhiBarInf Sf P.GB V F
  lam j := lam P.GB F j
  wn := wChoice P F
  νn := nuChoice P (Sf := Sf) (V := V) F
  hlam_pos := hA6.2
  hlam_sorted := hA6.1
  hwn_unit j := (wChoice_spec P F j).1
  hνn_unit j := (nuChoice_spec P hSf hA5 hV F hA6 j).1
  hwn_eig j := (wChoice_spec P F j).2
  hνn_eig j := (nuChoice_spec P hSf hA5 hV F hA6 j).2
  duality j := by
    have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by have := P.hkn; omega)
    have hsq : Real.sqrt ((n : ℝ) * lam P.GB F j) ≠ 0 :=
      (Real.sqrt_pos.2 (mul_pos hn (hA6.2 j))).ne'
    dsimp only
    rw [nuChoice, smul_smul, mul_one_div_cancel hsq, one_smul]

end limit

/-! ## Orthonormality of the sample eigenvectors -/

/-- For large `p`, the top-`k` eigenvalues of `S⁽ᵖ⁾` are distinct, so any choice of unit
eigenvectors `h₁, …, h_k` is orthonormal. -/
lemma eventually_hmat_orthonormal (hFact2n : Fact2_Weyl n) (P : LoadingParams k n)
    (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F) {Zarr : ℕ → Fin n → ℝ}
    (hW : Tendsto (fun p => Wdual P.Barr F Zarr p) atTop (𝓝 (Wlim P.GB F P.δ2)))
    (h : (p : ℕ) → Fin k → EuclideanSpace ℝ (Fin p))
    (hh : ∀ᶠ p in atTop, ∀ j, IsUnitEigvec (Scov P.Barr F Zarr p) (h p j)
      (sortedEigN (Scov P.Barr F Zarr p) j)) :
    ∀ᶠ p in atTop, (Hmat (h p))ᵀ * Hmat (h p) = 1 := by
  have hθlim := fun j : Fin k => theta_limit hFact2n P F hW j
  have hdist : ∀ᶠ p in atTop, ∀ i j : Fin k, i ≠ j →
      theta P.Barr F Zarr p i ≠ theta P.Barr F Zarr p j := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · have hne : lam P.GB F i + P.δ2 / n ≠ lam P.GB F j + P.δ2 / n := by
        intro he
        exact hij (hA6.1.injective (by simpa using he))
      filter_upwards [((hθlim i).sub (hθlim j)).eventually_ne (sub_ne_zero.2 hne)] with p hp _
      exact fun he => hp (by rw [he, sub_self])
  filter_upwards [hh, hdist] with p hp hd
  rw [hmat_eq_of_colVec]
  ext i j
  simp only [Matrix.of_apply, Matrix.one_apply]
  split_ifs with hij
  · subst hij
    rw [real_inner_self_eq_norm_sq, (hp i).1, one_pow]
  · refine inner_eq_zero_of_eigvec (scov_transpose P.Barr F Zarr p) (hp i).2 (hp j).2 ?_
    rw [sortedEigN_scov, sortedEigN_scov]
    exact hd i j hij

/-! ## The model along one noise path -/

theorem exists_model (hFact2k : Fact2_Weyl k) (hFact2n : Fact2_Weyl n) (P : LoadingParams k n)
    {Sf : Matrix (Fin k) (Fin k) ℝ} (hSf : Sf.PosDef) (hA5 : Assumption5 Sf P.GB)
    (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F)
    {V : Matrix (Fin k) (Fin k) ℝ} (hV : IsEigenbasis (Kmat Sf P.GB) V)
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
      (sortedEigN (Scov P.Barr F Zarr p) j)) :
    ∃ M : AsymptoticModel k n P.δ2,
      (∀ᶠ Q : Adm k in atTop, M.b Q = bs Q.1 ∧ M.h Q = h Q.1) ∧
      (∀ j, M.lam j = lam P.GB F j) ∧
      (∀ j, IsUnitEigvec (Nlim Sf P.GB V F) (M.νn j) (lam P.GB F j)) := by
  have hs : P.GBᵀ = P.GB := transpose_eq_of_isHermitian P.GB_posDef.isHermitian
  have hW : Tendsto (fun p => Wdual P.Barr F Zarr p) atTop (𝓝 (Wlim P.GB F P.δ2)) :=
    tendsto_wdual_of_parts (tendsto_w0p P F) hX hG
  have hθlim := fun j : Fin k => theta_limit hFact2n P F hW j
  -- eventual facts at each large `p`
  have hdet : ∀ᶠ p in atTop, IsUnit ((Bmat P.Barr p)ᵀ * Bmat P.Barr p).det := by
    have hc : Tendsto (fun p => (GBp P.Barr p).det) atTop (𝓝 P.GB.det) :=
      ((continuous_id.matrix_det).tendsto _).comp P.A4
    filter_upwards [hc.eventually_ne P.GB_posDef.det_pos.ne'] with p hp
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hp
    rw [GBp, Matrix.det_smul, h0, mul_zero]
  have hdist : ∀ᶠ p in atTop, ∀ i j : Fin k, i ≠ j →
      theta P.Barr F Zarr p i ≠ theta P.Barr F Zarr p j := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · have hne : lam P.GB F i + P.δ2 / n ≠ lam P.GB F j + P.δ2 / n := by
        intro he
        exact hij (hA6.1.injective (by simpa using he))
      filter_upwards [((hθlim i).sub (hθlim j)).eventually_ne (sub_ne_zero.2 hne)] with p hp _
      exact fun he => hp (by rw [he, sub_self])
  have hH : ∀ᶠ p in atTop, (Hmat (h p))ᵀ * Hmat (h p) = 1 := by
    filter_upwards [hh, hdist] with p hp hd
    rw [hmat_eq_of_colVec]
    ext i j
    simp only [Matrix.of_apply, Matrix.one_apply]
    split_ifs with hij
    · subst hij
      rw [real_inner_self_eq_norm_sq, (hp i).1, one_pow]
    · refine inner_eq_zero_of_eigvec (scov_transpose P.Barr F Zarr p) (hp i).2 (hp j).2 ?_
      rw [sortedEigN_scov, sortedEigN_scov]
      exact hd i j hij
  have hR : ∀ᶠ p in atTop, RealFacts P Sf F Zarr p (bs p) (h p) := by
    filter_upwards [eventually_ge_atTop k, eventually_pmu_pos hFact2k P hA5,
      eventually_kp_simple hFact2k P hA5, hbs, hdet, hh, hH] with p hkp hpp hK hb hd hhp hHp
    exact ⟨hkp, hpp.1, hpp.2, hK.1, hb, hd, hhp, hHp⟩
  obtain ⟨p0, hp0⟩ := eventually_atTop.1 hR
  -- the per-`p` data
  set L := limitData P hSf hA5 hV F hA6 with hL
  let Φs : (p : ℕ) → Matrix (Fin k) (Fin n) ℝ := fun p => PhiMat (bs p) (Bmat P.Barr p) F
  let Wm : ℕ → Matrix (Fin n) (Fin n) ℝ := fun p => (1 / ((n : ℝ) * p)) •
    ((bs p * Φs p + truncRows Zarr p)ᵀ * (bs p * Φs p + truncRows Zarr p))
  let Nm : ℕ → Matrix (Fin k) (Fin k) ℝ := fun p => (1 / ((n : ℝ) * p)) • (Φs p * (Φs p)ᵀ)
  let w0 : ℕ → Fin k → EuclideanSpace ℝ (Fin n) := fun p j =>
    colVec (eigenbasisOf (Wm p)) (Fin.castLE P.hkn.le j)
  let ν0 : ℕ → Fin k → EuclideanSpace ℝ (Fin k) := fun p j => colVec (eigenbasisOf (Nm p)) j
  let sw : ℕ → Fin k → ℝ := fun p j => sgn1 (inner ℝ (w0 p j) (wChoice P F j))
  let sν : ℕ → Fin k → ℝ := fun p j =>
    sgn1 (inner ℝ (ν0 p j) (nuChoice P (Sf := Sf) (V := V) F j))
  let D : (Q : Adm k) → PerP k n P.hkn F Sf Q.1 := fun Q =>
    if hQ : p0 ≤ Q.1 then
      realPerP P hSf F Zarr (hp0 Q.1 hQ) (sw Q.1) (sν Q.1) (fun _ => sgn1_pm _) (fun _ => sgn1_pm _)
    else glue hSf P.hkn F Q.2
  have hD : ∀ (Q : Adm k) (hQ : p0 ≤ Q.1), D Q =
      realPerP P hSf F Zarr (hp0 Q.1 hQ) (sw Q.1) (sν Q.1) (fun _ => sgn1_pm _)
        (fun _ => sgn1_pm _) := fun Q hQ => dif_pos hQ
  have hWm : ∀ p, p0 ≤ p → Wm p = Wdual P.Barr F Zarr p := fun p hp => (hp0 p hp).wdual_eq hSf
  -- the limit facts
  have f1 : Tendsto (fun Q : Adm k => (1 / ((n : ℝ) * Q.1)) • ((D Q).Zᵀ * (D Q).Z)) atTop
      (𝓝 ((P.δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
    refine tendsto_adm_of_eq p0 (f := fun p : ℕ => (1 / ((n : ℝ) * p)) •
      ((truncRows Zarr p)ᵀ * truncRows Zarr p)) (fun Q hQ => by rw [hD Q hQ]; rfl) ?_
    refine hG.congr fun p => ?_
    rw [smul_smul, one_div_mul_one_div]
  have f2 : Tendsto (fun Q : Adm k => (1 / Real.sqrt Q.1) • ((D Q).bᵀ * (D Q).Z)) atTop
      (𝓝 (0 : Matrix (Fin k) (Fin n) ℝ)) :=
    tendsto_adm_of_eq p0 (f := fun p : ℕ => (1 / Real.sqrt p) • ((bs p)ᵀ * truncRows Zarr p))
      (fun Q hQ => by rw [hD Q hQ]; rfl) hbZ
  have f3 : Tendsto (fun Q : Adm k => (1 / Real.sqrt Q.1) • (D Q).Φ) atTop (𝓝 L.Φbarinf) :=
    tendsto_adm_of_eq p0 (f := fun p : ℕ => (1 / Real.sqrt p) • Φs p)
      (fun Q hQ => by rw [hD Q hQ]; rfl) (tendsto_phibar hFact2k P hSf hA5 F hV hbs hsign)
  have f4a : ∀ j : Fin k, Tendsto (fun Q : Adm k => (D Q).θ (Fin.castLE (le_of_lt P.hkn) j))
      atTop (𝓝 (L.lam j + P.δ2 / n)) := fun j =>
    tendsto_adm_of_eq p0 (f := fun p => theta P.Barr F Zarr p j)
      (fun Q hQ => by
        rw [hD Q hQ]
        dsimp only
        rw [theta_eq_sortedEig _ _ _ _ P.hkn, ← hWm Q.1 hQ]
        rfl) (hθlim j)
  have f4b : Tendsto (fun Q : Adm k => (1 / ((n : ℝ) - k)) *
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), (D Q).θ i) atTop
      (𝓝 (P.δ2 / n)) := by
    refine tendsto_adm_of_eq p0 (f := fun p => (1 / ((n : ℝ) - k)) *
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)),
        sortedEig (Wdual P.Barr F Zarr p) i)
      (fun Q hQ => by rw [hD Q hQ]; dsimp only; rw [← hWm Q.1 hQ]; rfl) ?_
    have hsum : Tendsto (fun p => ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)),
        sortedEig (Wdual P.Barr F Zarr p) i) atTop
        (𝓝 (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), P.δ2 / n)) := by
      refine tendsto_finset_sum _ fun i hi => ?_
      have := tendsto_sortedEig hFact2n
        (fun p => isHermitian_of_transpose_eq (wdual_transpose P.Barr F Zarr p))
        (isHermitian_of_transpose_eq (wlim_transpose hs F P.δ2)) hW i
      rwa [sortedEig_wlim_ge P.GB_posDef F P.δ2 i (Finset.mem_filter.1 hi).2] at this
    have hnk : (n : ℝ) - k ≠ 0 := sub_ne_zero.2 (by exact_mod_cast P.hkn.ne')
    have hval : (1 / ((n : ℝ) - k)) *
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), P.δ2 / n = P.δ2 / n := by
      rw [Finset.sum_const, card_filter_fin_ge, nsmul_eq_mul, Nat.cast_sub P.hkn.le]
      field_simp
    rw [← hval]
    exact hsum.const_mul _
  have f5 : ∀ j : Fin k, Tendsto (fun Q : Adm k => (D Q).w j) atTop (𝓝 (L.wn j)) := by
    intro j
    have hu : ∀ p, ‖w0 p j‖ = 1 := fun p =>
      ((isEigenbasis_eigenbasisOf (gram_isHermitian _ _)).isUnitEigvec _).1
    have hwp : ∀ᶠ p in atTop, IsUnitEigvec (Wdual P.Barr F Zarr p) (w0 p j)
        (theta P.Barr F Zarr p j) := by
      filter_upwards [eventually_ge_atTop p0] with p hp
      have := (isEigenbasis_eigenbasisOf (gram_isHermitian (bs p * Φs p + truncRows Zarr p)
        (1 / ((n : ℝ) * p)))).isUnitEigvec (Fin.castLE P.hkn.le j)
      rw [theta_eq_sortedEig _ _ _ _ P.hkn, ← hWm p hp]
      exact this
    have habs := wdual_eigvec_limit hFact2n P F hA6 hW j (fun p => w0 p j) hwp _
      (wChoice_spec P F j)
    exact tendsto_adm_of_eq p0 (f := fun p => sw p j • w0 p j)
      (fun Q hQ => by rw [hD Q hQ]; rfl) (tendsto_sgn1_smul hu (wChoice_spec P F j).1 habs)
  have f6 : ∀ j : Fin k, Tendsto (fun Q : Adm k => (D Q).ν j) atTop (𝓝 (L.νn j)) := by
    intro j
    have hu : ∀ p, ‖ν0 p j‖ = 1 := fun p =>
      ((isEigenbasis_eigenbasisOf (gram'_isHermitian _ _)).isUnitEigvec _).1
    have hsimple : ∀ i, i ≠ j → sortedEig (Nlim Sf P.GB V F) i ≠ sortedEig (Nlim Sf P.GB V F) j := by
      intro i hij
      rw [sortedEig_nlim hSf hA5 hV, sortedEig_nlim hSf hA5 hV]
      exact hA6.1.injective.ne hij
    have hv : IsUnitEigvec (Nlim Sf P.GB V F) (nuChoice P (Sf := Sf) (V := V) F j)
        (sortedEig (Nlim Sf P.GB V F) j) := by
      rw [sortedEig_nlim hSf hA5 hV F j]
      exact nuChoice_spec P hSf hA5 hV F hA6 j
    have habs := (eigpair_convergence hFact2k (fun p => Nm p) (Nlim Sf P.GB V F)
      (fun p => gram'_isHermitian _ _) (nlim_isHermitian F)
      (tendsto_npn hFact2k P hSf hA5 F hV hbs hsign) j hsimple _ hv).2.2 (fun p => ν0 p j)
      (Eventually.of_forall fun p =>
        (isEigenbasis_eigenbasisOf (gram'_isHermitian _ _)).isUnitEigvec j)
    exact tendsto_adm_of_eq p0 (f := fun p => sν p j • ν0 p j)
      (fun Q hQ => by rw [hD Q hQ]; rfl) (tendsto_sgn1_smul hu hv.1 habs)
  have f7 : Tendsto (fun Q : Adm k => (1 / (Q.1 : ℝ)) • ((D Q).Bᵀ * (D Q).B)) atTop
      (𝓝 P.GB) :=
    tendsto_adm_of_eq p0 (f := fun p => GBp P.Barr p) (fun Q hQ => by rw [hD Q hQ]; rfl) P.A4
  refine ⟨modelOfPerP P.hk P.hkn P.δ2_pos hSf P.GB_posDef hA5 D L f1 f2 f3 f4a f4b f5 f6 f7,
    ?_, fun j => rfl, fun j => nuChoice_spec P hSf hA5 hV F hA6 j⟩
  rw [Filter.eventually_atTop]
  refine ⟨⟨max p0 k, le_max_right _ _⟩, fun Q hQ => ?_⟩
  have hQ' : p0 ≤ Q.1 := le_trans (le_max_left _ _) (show max p0 k ≤ Q.1 from hQ)
  exact ⟨by show (D Q).b = _; rw [hD Q hQ']; rfl, by show (D Q).h = _; rw [hD Q hQ']; rfl⟩

end PCError

end
