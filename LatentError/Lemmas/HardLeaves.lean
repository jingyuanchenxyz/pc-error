import LatentError.Lemmas.ThmLeaves
import LatentError.Lemmas.Easy
import LatentError.Lemmas.FactorSLLN

/-!
# Harder leaf lemmas (overnight campaign targets)

Targets for `harness/campaign.py`. Each lemma has an informal proof sketch in comments
(`-- sketch:`), written for the local prover.
* Proposition 3(a)–(d): the almost-sure limits.
* Corollary 3: the large-`n` limit of `N`.
* Remark after Corollary 3: one entry of `FFᵀ/n`.
* Lemma 6(i): the admissible covariances are the orthogonal orbit.
* Non-vacuity: the hypothesis bundles `LoadingParams`, `NoiseModel`, and Assumptions 5–6
  are inhabited, so no statement is vacuous.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix MatrixOrder

noncomputable section

namespace PCError

variable {k n : ℕ}

/-! ## Proposition 3: almost-sure limits of the noise terms -/

section noise

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {var : ℕ → Fin n → ℝ} {κ4 : ℝ}

theorem NoiseModel.gram_limit (N : NoiseModel n var κ4 Ω μ) (hFact1 : Fact1_SLLN) {δ2 : ℝ}
    (hA3 : ∀ l : Fin n, Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.range p, var i l)
      atTop (𝓝 δ2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (1 / (n : ℝ)) •
      ((1 / (p : ℝ)) • ((truncRows (N.path ω) p)ᵀ * truncRows (N.path ω) p)))
      atTop (𝓝 ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  -- sketch: intersect the entrywise almost-sure limits, then apply `tendsto_noise_gram`.
  -- have h1 : ∀ᵐ ω ∂μ, ∀ l, Tendsto (fun p : ℕ => (1 / (p : ℝ)) *
  --     ∑ i ∈ Finset.range p, N.Z i l ω ^ 2) atTop (𝓝 δ2) :=
  --   ae_all_iff.2 fun l => N.avg_sq hFact1 l (hA3 l)
  -- have h2 : ∀ᵐ ω ∂μ, ∀ l m, l ≠ m → Tendsto (fun p : ℕ => (1 / (p : ℝ)) *
  --     ∑ i ∈ Finset.range p, N.Z i l ω * N.Z i m ω) atTop (𝓝 0) := by
  --   refine ae_all_iff.2 fun l => ae_all_iff.2 fun m => ?_
  --   by_cases hlm : l = m
  --   · exact Eventually.of_forall fun ω h => absurd hlm h
  --   · filter_upwards [N.avg_cross hFact1 hlm] with ω hω using fun _ => hω
  -- filter_upwards [h1, h2] with ω hω1 hω2
  -- exact tendsto_noise_gram hω1 hω2      -- `N.path ω i l` is `N.Z i l ω` by definition
  have h1 : ∀ᵐ ω ∂μ, ∀ l, Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.range p, N.Z i l ω ^ 2) atTop (𝓝 δ2) :=
    ae_all_iff.2 fun l => N.avg_sq hFact1 l (hA3 l)
  have h2 : ∀ᵐ ω ∂μ, ∀ l m, l ≠ m → Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.range p, N.Z i l ω * N.Z i m ω) atTop (𝓝 0) := by
    refine ae_all_iff.2 fun l => ae_all_iff.2 fun m => ?_
    by_cases hlm : l = m
    · exact Eventually.of_forall fun ω h => absurd hlm h
    · filter_upwards [N.avg_cross hFact1 hlm] with ω hω using fun _ => hω
  filter_upwards [h1, h2] with ω hω1 hω2
  exact tendsto_noise_gram hω1 hω2

theorem NoiseModel.gram_limit_opNorm (N : NoiseModel n var κ4 Ω μ) (hFact1 : Fact1_SLLN)
    {δ2 : ℝ} (hA3 : ∀ l : Fin n, Tendsto (fun p : ℕ => (1 / (p : ℝ)) *
      ∑ i ∈ Finset.range p, var i l) atTop (𝓝 δ2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ =>
      opNorm ((1 / ((n : ℝ) * p)) • ((truncRows (N.path ω) p)ᵀ * truncRows (N.path ω) p) -
        (δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ))) atTop (𝓝 0) := by
  -- sketch: filter_upwards [N.gram_limit hFact1 hA3] with ω hω
  -- apply `tendsto_opNorm_sub` to hω after rewriting the scalars:
  -- (1/n) • (1/p) • M = (1/(n*p)) • M  (`smul_smul`, `one_div_mul_one_div`)
  filter_upwards [N.gram_limit hFact1 hA3] with ω hω
  refine tendsto_opNorm_sub (hω.congr fun p => ?_)
  rw [smul_smul, one_div_mul_one_div]

lemma gb_diag_pos (P : LoadingParams k n) (j : Fin k) : 0 < P.GB j j := by
  -- sketch: exact P.GB_posDef.diag_pos
  apply P.GB_posDef.diag_pos

lemma tendsto_colNorm_sq_div (P : LoadingParams k n) (j : Fin k) :
    Tendsto (fun p : ℕ => ‖colVec (Bmat P.Barr p) j‖ ^ 2 / p) atTop (𝓝 (P.GB j j)) := by
  -- sketch: the (j, j) entry is continuous, so GBp j j → GB j j:
  -- have h := (((continuous_apply j).comp (continuous_apply j)).tendsto P.GB).comp P.A4
  -- for p > 0, ‖colVec‖² / p = GBp j j (`gBp_apply_mul`: GBp j j * p = ‖colVec‖²):
  -- refine h.congr' ?_; filter_upwards [eventually_gt_atTop 0] with p hp
  -- rw [← gBp_apply_mul _ _ hp]; field_simp
  have h : Tendsto (fun p : ℕ => GBp P.Barr p j j) atTop (𝓝 (P.GB j j)) :=
    ((continuous_id.matrix_elem j j).tendsto P.GB).comp P.A4
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with p hp
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  show GBp P.Barr p j j = ‖colVec (Bmat P.Barr p) j‖ ^ 2 / p
  rw [← gBp_apply_mul P.Barr p hp j, mul_div_assoc, div_self hp', mul_one]

lemma eventually_colVec_ne_zero (P : LoadingParams k n) (j : Fin k) :
    ∀ᶠ p in atTop, colVec (Bmat P.Barr p) j ≠ 0 := by
  -- sketch: ‖colVec‖²/p → GB j j > 0 (`tendsto_colNorm_sq_div`, `gb_diag_pos`), so eventually
  -- ‖colVec‖²/p > 0: `(tendsto_colNorm_sq_div P j).eventually (lt_mem_nhds (gb_diag_pos P j))`;
  -- if colVec = 0 the quotient would be 0.
  filter_upwards [(tendsto_colNorm_sq_div P j).eventually (lt_mem_nhds (gb_diag_pos P j))] with p hp
  intro h0
  rw [h0, norm_zero] at hp
  simp at hp

lemma tendsto_colNorm_div_sqrt (P : LoadingParams k n) (j : Fin k) :
    Tendsto (fun p : ℕ => ‖colVec (Bmat P.Barr p) j‖ / Real.sqrt p) atTop
      (𝓝 (Real.sqrt (P.GB j j))) := by
  -- sketch: exact tendsto_norm_div_sqrt (fun p => norm_nonneg _) (tendsto_colNorm_sq_div P j)
  apply tendsto_norm_div_sqrt
  · intro p
    exact norm_nonneg _
  · exact tendsto_colNorm_sq_div P j

theorem NoiseModel.cross_entry_limit (N : NoiseModel n var κ4 Ω μ) (P : LoadingParams k n)
    (j : Fin k) (l : Fin n) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (∑ i : Fin p, Bmat P.Barr p i j * N.Z i l ω) / p) atTop
      (𝓝 0) := by
  -- sketch: v p := colVec (Bmat P.Barr p) j, a p := ‖v p‖⁻¹ • v p.
  -- a p is eventually a unit vector (`eventually_colVec_ne_zero`, `norm_inv_smul_self`), so
  -- Lemma 4 (`N.concentration a ha l`) gives (∑ i, a p i * Z i l) / √p → 0 a.s.
  -- ∑ i, a p i * Z i l = (∑ i, v p i * Z i l) / ‖v p‖ (`sum_inv_smul_mul`), and v p i = B i j
  -- (`colVec`, by rfl or simp). Conclude with `tendsto_div_of_normalized`
  -- (S p := ∑ i, B i j * Z i l, r p := ‖v p‖), using `norm_ne_zero_iff` and
  -- `tendsto_colNorm_div_sqrt`.
  have hne := eventually_colVec_ne_zero P j
  have ha : ∀ᶠ p in atTop, ‖‖colVec (Bmat P.Barr p) j‖⁻¹ • colVec (Bmat P.Barr p) j‖ = 1 :=
    hne.mono fun p hp => norm_inv_smul_self _ hp
  filter_upwards [N.concentration
    (fun p => ‖colVec (Bmat P.Barr p) j‖⁻¹ • colVec (Bmat P.Barr p) j) ha l] with ω hω
  refine tendsto_div_of_normalized (r := fun p => ‖colVec (Bmat P.Barr p) j‖)
    (hne.mono fun p hp => norm_ne_zero_iff.2 hp) ?_ (tendsto_colNorm_div_sqrt P j)
  refine hω.congr fun p => ?_
  rw [sum_inv_smul_mul]
  rfl

theorem NoiseModel.cross_limit (N : NoiseModel n var κ4 Ω μ) (P : LoadingParams k n) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ =>
      (1 / (p : ℝ)) • ((Bmat P.Barr p)ᵀ * truncRows (N.path ω) p)) atTop (𝓝 0) := by
  -- sketch: have h : ∀ᵐ ω ∂μ, ∀ j l, Tendsto (fun p : ℕ =>
  --     (∑ i : Fin p, Bmat P.Barr p i j * N.Z i l ω) / p) atTop (𝓝 0) :=
  --   ae_all_iff.2 fun j => ae_all_iff.2 fun l => N.cross_entry_limit P j l
  -- filter_upwards [h] with ω hω
  -- refine tendsto_matrix_of_entries fun j l => ?_
  -- simpa [smul_transpose_mul_truncRows_apply] using hω j l
  have h : ∀ᵐ ω ∂μ, ∀ j l, Tendsto (fun p : ℕ =>
      (∑ i : Fin p, Bmat P.Barr p i j * N.Z i l ω) / p) atTop (𝓝 0) :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun l => N.cross_entry_limit P j l
  filter_upwards [h] with ω hω
  refine tendsto_matrix_of_entries fun j l => ?_
  refine (hω j l).congr fun p => ?_
  rw [smul_transpose_mul_truncRows_apply]

lemma frobSq_transpose_mul_truncRows {p c : ℕ} (b : Matrix (Fin p) (Fin k) ℝ)
    (A : ℕ → Fin c → ℝ) :
    frobSq (bᵀ * truncRows A p) = ∑ j, ∑ l, (∑ i : Fin p, b i j * A i l) ^ 2 := by
  -- sketch: simp only [frobSq, transpose_mul_truncRows_apply]
  rfl

lemma sqrt_sum_sq_div_tendsto {a b : ℕ} {x : Fin a → Fin b → ℕ → ℝ}
    (h : ∀ j l, Tendsto (fun p : ℕ => x j l p / Real.sqrt p) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ => Real.sqrt (∑ j, ∑ l, x j l p ^ 2) / Real.sqrt p) atTop (𝓝 0) := by
  -- sketch: √(Σ x²)/√p = √(Σ (x/√p)²) for p ≥ 0 (`Real.sqrt_div'`, `Finset.sum_div`, `div_pow`,
  -- `Real.sq_sqrt`). The inner sum → 0 by `tendsto_finset_sum` and `(h j l).pow 2`;
  -- then `Tendsto.sqrt`, and `Real.sqrt_zero`.
  have h2 : Tendsto (fun p : ℕ => ∑ j, ∑ l, (x j l p / Real.sqrt p) ^ 2) atTop
      (𝓝 (∑ j : Fin a, ∑ l : Fin b, (0 : ℝ) ^ 2)) :=
    tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun l _ => (h j l).pow 2
  rw [show (∑ j : Fin a, ∑ l : Fin b, (0 : ℝ) ^ 2) = 0 by simp] at h2
  have h3 := h2.sqrt
  rw [Real.sqrt_zero] at h3
  refine h3.congr fun p => ?_
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  simp only [div_pow, Real.sq_sqrt hp, ← Finset.sum_div]
  exact Real.sqrt_div' _ hp

theorem NoiseModel.frob_limit (N : NoiseModel n var κ4 Ω μ)
    (b : (p : ℕ) → Matrix (Fin p) (Fin k) ℝ) (hb : ∀ᶠ p in atTop, (b p)ᵀ * b p = 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ =>
      Real.sqrt (frobSq ((b p)ᵀ * truncRows (N.path ω) p)) / Real.sqrt p) atTop (𝓝 0) := by
  -- sketch: for each column j, a p := colVec (b p) j is eventually a unit vector
  -- (filter_upwards [hb] with p hp using norm_colVec (b p) hp j), so Lemma 4
  -- (`N.concentration`) gives (∑ i, b p i j * Z i l) / √p → 0 a.s. for each (j, l).
  -- Intersect over (j, l) with `ae_all_iff`, rewrite with `frobSq_transpose_mul_truncRows`,
  -- and conclude with `sqrt_sum_sq_div_tendsto`.
  have hu : ∀ j : Fin k, ∀ᶠ p in atTop, ‖colVec (b p) j‖ = 1 := fun j =>
    hb.mono fun p hp => norm_colVec (b p) hp j
  have h : ∀ᵐ ω ∂μ, ∀ j l, Tendsto (fun p : ℕ =>
      (∑ i : Fin p, colVec (b p) j i * N.Z i l ω) / Real.sqrt p) atTop (𝓝 0) :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun l => N.concentration (fun p => colVec (b p) j) (hu j) l
  filter_upwards [h] with ω hω
  refine (sqrt_sum_sq_div_tendsto
    (x := fun j l p => ∑ i : Fin p, b p i j * N.Z i l ω) hω).congr fun p => ?_
  rw [frobSq_transpose_mul_truncRows]

end noise

/-! ## Proposition 3(c)–(d): spectrum of `W` and the eigenvalue limits -/

lemma sortedEig_wlim_lt {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GB.PosDef)
    (F : Matrix (Fin k) (Fin n) ℝ) (δ2 : ℝ) (i : Fin n) (hi : (i : ℕ) < k) :
    sortedEig (Wlim GB F δ2) i = lam GB F i + δ2 / n := by
  -- sketch: rw [sortedEig_wlim (transpose_eq_of_isHermitian hGB.isHermitian)]
  -- then lam GB F i = sortedEigN (W0 GB F) i = sortedEig (W0 GB F) i (`lam`, `sortedEigN_fin`)
  rw [sortedEig_wlim (transpose_eq_of_isHermitian hGB.isHermitian)]
  simp [lam, sortedEigN_fin (W0 GB F) (i : ℕ) (by simpa using hi)]

lemma sortedEig_wlim_ge {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GB.PosDef)
    (F : Matrix (Fin k) (Fin n) ℝ) (δ2 : ℝ) (i : Fin n) (hi : k ≤ (i : ℕ)) :
    sortedEig (Wlim GB F δ2) i = δ2 / n := by
  -- sketch: as in `sortedEig_wlim_lt`; sortedEig (W0 GB F) i = sortedEigN (W0 GB F) i = 0
  -- by `sortedEigN_fin` and `sortedEigN_w0_eq_zero hGB F i hi`
  have h0 : sortedEig (W0 GB F) i = 0 := by
    have := sortedEigN_w0_eq_zero hGB F i hi
    simpa [sortedEigN, i.2] using this
  rw [sortedEig_wlim (transpose_eq_of_isHermitian hGB.isHermitian)]
  simp [h0]

lemma isUnitEigvec_wlim {GB : Matrix (Fin k) (Fin k) ℝ} (F : Matrix (Fin k) (Fin n) ℝ)
    (δ2 : ℝ) (w : EuclideanSpace ℝ (Fin n)) (lamj : ℝ) (hw : IsUnitEigvec (W0 GB F) w lamj) :
    IsUnitEigvec (Wlim GB F δ2) w (lamj + δ2 / n) := by
  -- sketch: refine ⟨hw.1, ?_⟩; unfold Wlim
  -- rw [map_add, LinearMap.add_apply, toEuclideanLin_smul_apply, toEuclideanLin_one_apply, hw.2,
  --   add_smul]
  refine ⟨hw.1, ?_⟩
  unfold Wlim
  simp [Matrix.add_apply, toEuclideanLin_smul_apply, toEuclideanLin_one_apply, hw.2]
  simp [add_smul]

theorem theta_limit (hFact2n : Fact2_Weyl n) (P : LoadingParams k n)
    (F : Matrix (Fin k) (Fin n) ℝ) {Zarr : ℕ → Fin n → ℝ}
    (hW : Tendsto (fun p => Wdual P.Barr F Zarr p) atTop (𝓝 (Wlim P.GB F P.δ2)))
    (j : Fin k) :
    Tendsto (fun p => theta P.Barr F Zarr p j) atTop (𝓝 (lam P.GB F j + P.δ2 / n)) := by
  -- sketch: i : Fin n := ⟨j, lt_trans j.2 P.hkn⟩. Then theta P.Barr F Zarr p j =
  -- sortedEigN (Wdual ..) j = sortedEig (Wdual ..) i (`theta`, `sortedEigN_fin`).
  -- `tendsto_sortedEig hFact2n` gives the limit sortedEig (Wlim ..) i, using
  -- `isHermitian_of_transpose_eq (wdual_transpose ..)` and
  -- `isHermitian_of_transpose_eq (wlim_transpose hs ..)` with
  -- hs := transpose_eq_of_isHermitian P.GB_posDef.isHermitian.
  -- That limit is `sortedEig_wlim_lt P.GB_posDef F P.δ2 i j.2`.
  have hs : P.GBᵀ = P.GB := transpose_eq_of_isHermitian P.GB_posDef.isHermitian
  have hjn : (j : ℕ) < n := lt_trans j.2 P.hkn
  have h := tendsto_sortedEig hFact2n
    (fun p => isHermitian_of_transpose_eq (wdual_transpose P.Barr F Zarr p))
    (isHermitian_of_transpose_eq (wlim_transpose hs F P.δ2)) hW ⟨j, hjn⟩
  rw [sortedEig_wlim_lt P.GB_posDef F P.δ2 ⟨j, hjn⟩ j.2] at h
  refine h.congr fun p => ?_
  show _ = sortedEigN (Wdual P.Barr F Zarr p) j
  rw [sortedEigN_fin _ _ hjn]

lemma wlim_simple (P : LoadingParams k n) (F : Matrix (Fin k) (Fin n) ℝ)
    (hA6 : Assumption6 P.GB F) (j : Fin k) :
    ∀ i : Fin n, i ≠ ⟨j, lt_trans j.2 P.hkn⟩ →
      sortedEig (Wlim P.GB F P.δ2) i ≠ sortedEig (Wlim P.GB F P.δ2) ⟨j, lt_trans j.2 P.hkn⟩ := by
  -- sketch: the right side is lam j + δ²/n (`sortedEig_wlim_lt`). If (i : ℕ) < k, the left side
  -- is lam i' + δ²/n with i' := ⟨i, _⟩ ≠ j, and lam is injective on Fin k (hA6.1.injective).
  -- If k ≤ i, the left side is δ²/n (`sortedEig_wlim_ge`) and lam j > 0 (hA6.2 j).
  intro i hi
  have hjn : (j : ℕ) < n := lt_trans j.2 P.hkn
  rw [sortedEig_wlim_lt P.GB_posDef F P.δ2 ⟨j, hjn⟩ j.2]
  by_cases hik : (i : ℕ) < k
  · rw [sortedEig_wlim_lt P.GB_posDef F P.δ2 i hik]
    intro h
    have h1 : lam P.GB F ((⟨i, hik⟩ : Fin k) : ℕ) = lam P.GB F (j : ℕ) := by simpa using h
    have h2 := hA6.1.injective h1
    exact hi (Fin.ext (by simpa using congrArg Fin.val h2))
  · rw [sortedEig_wlim_ge P.GB_posDef F P.δ2 i (not_lt.1 hik)]
    intro h
    have h' : lam P.GB F (j : ℕ) = 0 := by simpa using h
    linarith [hA6.2 j]

theorem wdual_eigvec_limit (hFact2n : Fact2_Weyl n) (P : LoadingParams k n)
    (F : Matrix (Fin k) (Fin n) ℝ) (hA6 : Assumption6 P.GB F) {Zarr : ℕ → Fin n → ℝ}
    (hW : Tendsto (fun p => Wdual P.Barr F Zarr p) atTop (𝓝 (Wlim P.GB F P.δ2)))
    (j : Fin k) (wp : ℕ → EuclideanSpace ℝ (Fin n))
    (hwp : ∀ᶠ p in atTop, IsUnitEigvec (Wdual P.Barr F Zarr p) (wp p) (theta P.Barr F Zarr p j))
    (w : EuclideanSpace ℝ (Fin n)) (hw : IsUnitEigvec (W0 P.GB F) w (lam P.GB F j)) :
    Tendsto (fun p => |inner ℝ (wp p) w|) atTop (𝓝 1) := by
  -- sketch: Lemma 2(i): `(eigpair_convergence hFact2n (fun p => Wdual ..) (Wlim ..) hA hAinf hW
  --   i (wlim_simple P F hA6 j) w hv).2.2 wp hwp'` with i := ⟨j, lt_trans j.2 P.hkn⟩.
  -- hA, hAinf: `isHermitian_of_transpose_eq` with `wdual_transpose` / `wlim_transpose`.
  -- hv : IsUnitEigvec (Wlim ..) w (sortedEig (Wlim ..) i): from `isUnitEigvec_wlim F P.δ2 w _ hw`
  -- and `sortedEig_wlim_lt P.GB_posDef F P.δ2 i j.2`.
  -- hwp': theta P.Barr F Zarr p j = sortedEig (Wdual ..) i (`theta`, `sortedEigN_fin`).
  have hs : P.GBᵀ = P.GB := transpose_eq_of_isHermitian P.GB_posDef.isHermitian
  have hjn : (j : ℕ) < n := lt_trans j.2 P.hkn
  have hv : IsUnitEigvec (Wlim P.GB F P.δ2) w (sortedEig (Wlim P.GB F P.δ2) ⟨j, hjn⟩) := by
    rw [sortedEig_wlim_lt P.GB_posDef F P.δ2 ⟨j, hjn⟩ j.2]
    exact isUnitEigvec_wlim F P.δ2 w _ hw
  have hwp' : ∀ᶠ p in atTop, IsUnitEigvec (Wdual P.Barr F Zarr p) (wp p)
      (sortedEig (Wdual P.Barr F Zarr p) ⟨j, hjn⟩) := by
    filter_upwards [hwp] with p hp
    rwa [theta, sortedEigN_fin _ _ hjn] at hp
  exact (eigpair_convergence hFact2n (fun p => Wdual P.Barr F Zarr p) (Wlim P.GB F P.δ2)
    (fun p => isHermitian_of_transpose_eq (wdual_transpose P.Barr F Zarr p))
    (isHermitian_of_transpose_eq (wlim_transpose hs F P.δ2)) hW ⟨j, hjn⟩
    (wlim_simple P F hA6 j) w hv).2.2 wp hwp'

/-! ## Corollary 3 -/

section cor3

variable {Sf GB V : Matrix (Fin k) (Fin k) ℝ}

theorem nlim_tendsto_lamDiag (hSf : Sf.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) (f : ℕ → Fin k → ℝ)
    (hf : Tendsto (fun n : ℕ => (1 / (n : ℝ)) • (Fcols f n * (Fcols f n)ᵀ)) atTop (𝓝 Sf)) :
    Tendsto (fun n => Nlim Sf GB V (Fcols f n)) atTop (𝓝 (LamDiag Sf GB)) := by
  -- sketch: Nlim .. (Fcols f n) = Q * ((1/n) • (F Fᵀ)) * Qᵀ with Q := Qmat Sf GB V
  -- (`qmat_sigmaHat`, rewrite under `funext`). By `tendsto_conj Q hf` the limit is
  -- Q * Sf * Qᵀ, which is `LamDiag Sf GB` by `qmat_sf_qmat hSf hA5 hV`.
  have h := tendsto_conj (Qmat Sf GB V) hf
  rw [qmat_sf_qmat hSf hA5 hV] at h
  exact h.congr fun n => qmat_sigmaHat (Fcols f n)

theorem lam_tendsto_mu (hFact2k : Fact2_Weyl k) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) (f : ℕ → Fin k → ℝ)
    (hf : Tendsto (fun n : ℕ => (1 / (n : ℝ)) • (Fcols f n * (Fcols f n)ᵀ)) atTop (𝓝 Sf))
    (j : Fin k) :
    Tendsto (fun n => lam GB (Fcols f n) j) atTop (𝓝 (sortedEig (Kmat Sf GB) j)) := by
  -- sketch: lam GB (Fcols f n) j = sortedEig (Nlim ..) j (`sortedEig_nlim`, reversed).
  -- `tendsto_sortedEig hFact2k (fun n => nlim_isHermitian _) (lamDiag_isHermitian _ _)
  --   (nlim_tendsto_lamDiag ..) j` gives the limit sortedEig (LamDiag ..) j, which is
  -- sortedEig (Kmat ..) j by `sortedEig_lamDiag`.
  have h := tendsto_sortedEig hFact2k (fun n => nlim_isHermitian (Sf := Sf) (GB := GB) (V := V)
    (Fcols f n)) (lamDiag_isHermitian Sf GB) (nlim_tendsto_lamDiag hSf hA5 hV f hf) j
  rw [sortedEig_lamDiag] at h
  exact h.congr fun n => sortedEig_nlim hSf hA5 hV (Fcols f n) j

theorem nu_tendsto_axis (hFact2k : Fact2_Weyl k) (hSf : Sf.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) (f : ℕ → Fin k → ℝ)
    (hf : Tendsto (fun n : ℕ => (1 / (n : ℝ)) • (Fcols f n * (Fcols f n)ᵀ)) atTop (𝓝 Sf))
    (j : Fin k) (ν : ℕ → EuclideanSpace ℝ (Fin k))
    (hν : ∀ᶠ n in atTop, IsUnitEigvec (Nlim Sf GB V (Fcols f n)) (ν n)
      (sortedEig (Nlim Sf GB V (Fcols f n)) j)) :
    Tendsto (fun n => sinSq (ν n) (e j)) atTop (𝓝 0) := by
  -- sketch: Lemma 2(i) (`eigpair_convergence hFact2k`) for A n := Nlim .. (Fcols f n) and
  -- Ainf := LamDiag Sf GB (`nlim_tendsto_lamDiag`). Index j is simple because
  -- sortedEig (LamDiag ..) = sortedEig (Kmat ..) (`sortedEig_lamDiag`) is StrictAnti (hA5.1).
  -- `e j` is a unit eigenvector of LamDiag at that eigenvalue (`isUnitEigvec_diagonal_e`;
  -- LamDiag is `Matrix.diagonal (sortedEig (Kmat Sf GB))` by definition).
  -- The third conclusion gives |⟨ν n, e j⟩| → 1; finish with
  -- `sinSq_tendsto_zero_of_abs_inner` (‖e j‖ = 1 by simp; ‖ν n‖ = 1 eventually from hν).
  have hsimple : ∀ i, i ≠ j → sortedEig (LamDiag Sf GB) i ≠ sortedEig (LamDiag Sf GB) j := by
    intro i hi
    rw [sortedEig_lamDiag]
    exact hA5.1.injective.ne hi
  have hv : IsUnitEigvec (LamDiag Sf GB) (e j) (sortedEig (LamDiag Sf GB) j) := by
    rw [sortedEig_lamDiag]
    exact isUnitEigvec_diagonal_e _ j
  have h := (eigpair_convergence hFact2k (fun n => Nlim Sf GB V (Fcols f n)) (LamDiag Sf GB)
    (fun n => nlim_isHermitian _) (lamDiag_isHermitian Sf GB)
    (nlim_tendsto_lamDiag hSf hA5 hV f hf) j hsimple (e j) hv).2.2 ν hν
  exact sinSq_tendsto_zero_of_abs_inner (hν.mono fun n hn => hn.1) (by simp [e]) h

end cor3

/-! ## Lemma 6(i): the admissible covariances form one orthogonal orbit -/

section lemma6

variable {Sf GB : Matrix (Fin k) (Fin k) ℝ}

theorem sortedEig_orthogonal_conj {d : Fin k → ℝ} (hd : Antitone d)
    {O : Matrix (Fin k) (Fin k) ℝ} (hO : O ∈ Matrix.orthogonalGroup (Fin k) ℝ) :
    sortedEig (Oᵀ * Matrix.diagonal d * O) = d := by
  -- sketch: `sortedEig_eq_of_mul_eq` with U := Oᵀ. From `Matrix.mem_orthogonalGroup_iff`,
  -- O * Oᵀ = 1, so (Oᵀ)ᵀ * Oᵀ = O * Oᵀ = 1 and (Oᵀ D O) * Oᵀ = Oᵀ * D (`Matrix.mul_assoc`).
  apply sortedEig_eq_of_mul_eq (U := Oᵀ)
  · rw [Matrix.transpose_transpose, ← Matrix.mem_orthogonalGroup_iff]
    exact hO
  · exact hd
  · rw [Matrix.mul_assoc]
    rw [Matrix.mem_orthogonalGroup_iff] at hO
    rw [hO]
    simp

theorem sortedEig_kmat_eq {Sig : Matrix (Fin k) (Fin k) ℝ} (hSig : Sig.PosDef)
    (hGB : GB.PosDef) :
    sortedEig (Kmat Sig GB) = sortedEig (CFC.sqrt GB * Sig * CFC.sqrt GB) := by
  -- sketch: A := CFC.sqrt GB * CFC.sqrt Sig. Then A * Aᵀ = √GB * Sig * √GB and
  -- Aᵀ * A = √Sig * GB * √Sig = Kmat Sig GB (`sqrt_transpose`, `sqrt_mul_sqrt`,
  -- `Matrix.mul_assoc`). Gram duality `sortedEigN_mul_transpose A` equates the padded
  -- spectra; for square matrices this gives equal `sortedEig`
  -- (funext j; `congrFun _ j` and `sortedEigN_fin`).
  have h1 : (CFC.sqrt GB * CFC.sqrt Sig) * (CFC.sqrt GB * CFC.sqrt Sig)ᵀ =
      CFC.sqrt GB * Sig * CFC.sqrt GB := by
    rw [Matrix.transpose_mul, sqrt_transpose, sqrt_transpose,
      show CFC.sqrt GB * CFC.sqrt Sig * (CFC.sqrt Sig * CFC.sqrt GB) =
        CFC.sqrt GB * (CFC.sqrt Sig * CFC.sqrt Sig) * CFC.sqrt GB by
        simp only [Matrix.mul_assoc],
      sqrt_mul_sqrt hSig]
  have h2 : (CFC.sqrt GB * CFC.sqrt Sig)ᵀ * (CFC.sqrt GB * CFC.sqrt Sig) = Kmat Sig GB := by
    rw [Matrix.transpose_mul, sqrt_transpose, sqrt_transpose,
      show CFC.sqrt Sig * CFC.sqrt GB * (CFC.sqrt GB * CFC.sqrt Sig) =
        CFC.sqrt Sig * (CFC.sqrt GB * CFC.sqrt GB) * CFC.sqrt Sig by
        simp only [Matrix.mul_assoc],
      sqrt_mul_sqrt hGB, Kmat]
  funext j
  have := congrFun (sortedEigN_mul_transpose (CFC.sqrt GB * CFC.sqrt Sig)) j
  rw [h1, h2, sortedEigN_fin _ _ j.2, sortedEigN_fin _ _ j.2] at this
  exact this.symm

theorem sigmaO_posDef (hGB : GB.PosDef) {d : Fin k → ℝ} (hd : ∀ j, 0 < d j)
    {O : Matrix (Fin k) (Fin k) ℝ} (hO : O ∈ Matrix.orthogonalGroup (Fin k) ℝ) :
    (SigmaO GB (Matrix.diagonal d) O).PosDef := by
  -- sketch: SigmaO = Xᴴ * D * X with X := O * (CFC.sqrt GB)⁻¹; over ℝ, Xᴴ = Xᵀ
  -- (`Matrix.conjTranspose_eq_transpose_of_trivial`), and ((√GB)⁻¹)ᵀ = (√GB)⁻¹
  -- (`Matrix.transpose_nonsing_inv`, `sqrt_transpose`). D is PosDef
  -- (`Matrix.posDef_diagonal_iff`). X is invertible (O orthogonal, `sqrt_inv_mul`), so
  -- `X.mulVec` is injective; conclude with `Matrix.PosDef.conjTranspose_mul_mul_same`.
  have hOO : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).1 hO
  have hinv : ((CFC.sqrt GB)⁻¹)ᵀ = (CFC.sqrt GB)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, sqrt_transpose]
  have hYX : (CFC.sqrt GB * Oᵀ) * (O * (CFC.sqrt GB)⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Oᵀ, hOO, Matrix.one_mul, sqrt_mul_inv hGB]
  have hinj : Function.Injective (O * (CFC.sqrt GB)⁻¹).mulVec := by
    intro v w hvw
    have := congrArg (CFC.sqrt GB * Oᵀ).mulVec hvw
    simpa only [Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec] using this
  have h := (Matrix.posDef_diagonal_iff.2 hd).conjTranspose_mul_mul_same hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hinv] at h
  simpa only [SigmaO, Matrix.mul_assoc] using h

theorem sigmaO_admissible (hSf : Sf.PosDef) (hGB : GB.PosDef) (hA5 : Assumption5 Sf GB)
    {O : Matrix (Fin k) (Fin k) ℝ} (hO : O ∈ Matrix.orthogonalGroup (Fin k) ℝ) :
    Admissible Sf GB (SigmaO GB (LamDiag Sf GB) O) := by
  -- sketch: PosDef by `sigmaO_posDef hGB hA5.2 hO` (LamDiag is `Matrix.diagonal (sortedEig ..)`).
  -- Spectrum: rw [sortedEig_kmat_eq (that PosDef) hGB, sqrt_gb_sigmaO hGB],
  -- then `sortedEig_orthogonal_conj hA5.1.antitone hO`.
  have hPosDef : (SigmaO GB (LamDiag Sf GB) O).PosDef := by
    apply sigmaO_posDef hGB
    exact hA5.2
    exact hO
  have hSpec : sortedEig (Kmat (SigmaO GB (LamDiag Sf GB) O) GB) = sortedEig (Kmat Sf GB) := by
    rw [sortedEig_kmat_eq hPosDef hGB]
    rw [sqrt_gb_sigmaO hGB]
    apply sortedEig_orthogonal_conj
    exact hA5.1.antitone
    exact hO
  constructor
  · exact hPosDef
  · exact hSpec

theorem admissible_eq_sigmaO (hSf : Sf.PosDef) (hGB : GB.PosDef) (hA5 : Assumption5 Sf GB)
    {Sig : Matrix (Fin k) (Fin k) ℝ} (h : Admissible Sf GB Sig) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin k) ℝ, Sig = SigmaO GB (LamDiag Sf GB) O := by
  -- sketch: M := √GB * Sig * √GB is symmetric (`sqrt_transpose`, `transpose_eq_of_isHermitian`)
  -- with sortedEig M = sortedEig (Kmat Sf GB) (`sortedEig_kmat_eq h.1 hGB` and h.2).
  -- `exists_isEigenbasis` gives U with IsEigenbasis M U, so
  -- M = U * diagonal (sortedEig M) * Uᵀ (`IsEigenbasis.decomp`), i.e. M = U * Λ * Uᵀ.
  -- Take O := Uᵀ (orthogonal: `Matrix.mem_orthogonalGroup_iff'`, hU.1). Then
  -- Sig = (√GB)⁻¹ * M * (√GB)⁻¹ (`sqrt_inv_mul hGB`, `sqrt_mul_inv hGB`) = SigmaO GB Λ O.
  have hMs : (CFC.sqrt GB * Sig * CFC.sqrt GB).IsHermitian := by
    refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_mul, Matrix.transpose_mul, sqrt_transpose,
      transpose_eq_of_isHermitian h.1.isHermitian, Matrix.mul_assoc]
  obtain ⟨U, hU⟩ := exists_isEigenbasis hMs
  have hdec := hU.decomp
  rw [← sortedEig_kmat_eq h.1 hGB, h.2] at hdec
  refine ⟨Uᵀ, ?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_transpose]
    exact hU.1
  · have hSig : Sig = (CFC.sqrt GB)⁻¹ * (CFC.sqrt GB * Sig * CFC.sqrt GB) *
        (CFC.sqrt GB)⁻¹ := by
      simp only [← Matrix.mul_assoc]
      rw [sqrt_inv_mul hGB, Matrix.one_mul, Matrix.mul_assoc, sqrt_mul_inv hGB, Matrix.mul_one]
    rw [hSig, hdec]
    simp only [SigmaO, LamDiag, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem exists_eigenbasis_nlim_sigmaO (hSf : Sf.PosDef) (hGB : GB.PosDef)
    (hA5 : Assumption5 Sf GB) (F : Matrix (Fin k) (Fin n) ℝ)
    {O : Matrix (Fin k) (Fin k) ℝ} (hO : O ∈ Matrix.orthogonalGroup (Fin k) ℝ) :
    ∃ V, IsEigenbasis (Kmat (SigmaO GB (LamDiag Sf GB) O) GB) V ∧
      Nlim (SigmaO GB (LamDiag Sf GB) O) GB V F = O * Mhat GB F * Oᵀ := by
  -- sketch (paper, proof of Lemma 6(ii)): Σ := Σ_O, Λ := LamDiag Sf GB = diagonal μ, and
  -- A := √GB * √Σ, so A * Aᵀ = √GB Σ √GB = Oᵀ Λ O (`sqrt_gb_sigmaO`) and Aᵀ * A = K(Σ).
  -- V := Aᵀ * Oᵀ * diagonal (fun j => 1 / √μ_j). Then Vᵀ V = 1 and K(Σ) V = V Λ, and
  -- sortedEig K(Σ) = μ (`sigmaO_admissible`), so IsEigenbasis K(Σ) V.
  -- By `qmat_sigmaHat`, Nlim Σ GB V F = Q * ((1/n) • (F Fᵀ)) * Qᵀ with
  -- Q := Qmat Σ GB V = diagonal √μ * Vᵀ * (√Σ)⁻¹, and Q = O * √GB
  -- (Vᵀ = diagonal (1/√μ) * O * A, A * (√Σ)⁻¹ = √GB). So Nlim = O * Mhat GB F * Oᵀ
  -- (`Mhat`, `sqrt_transpose`, `Matrix.mem_orthogonalGroup_iff`).
  set μ := sortedEig (Kmat Sf GB) with hμ
  set Sig := SigmaO GB (LamDiag Sf GB) O with hSigdef
  set s := CFC.sqrt GB with hs
  set t := CFC.sqrt Sig with ht
  set Λ := Matrix.diagonal μ with hΛ
  set Di := Matrix.diagonal (fun j => 1 / Real.sqrt (μ j)) with hDi
  set Dh := Matrix.diagonal (fun j => Real.sqrt (μ j)) with hDh
  have hSig : Sig.PosDef := sigmaO_posDef hGB hA5.2 hO
  have hadm : Admissible Sf GB Sig := sigmaO_admissible hSf hGB hA5 hO
  have hOO : O * Oᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hO
  have hsq : ∀ j, Real.sqrt (μ j) ≠ 0 := fun j => (Real.sqrt_pos.2 (hA5.2 j)).ne'
  -- right-associated rewriting rules
  have k1 : ∀ X, s * (t * (t * (s * X))) = Oᵀ * (Λ * (O * X)) := by
    intro X
    have e1 : s * Sig * s = Oᵀ * Λ * O := sqrt_gb_sigmaO hGB _ _
    rw [← Matrix.mul_assoc t t, sqrt_mul_sqrt hSig]
    calc s * (Sig * (s * X)) = (s * Sig * s) * X := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e1]; simp only [Matrix.mul_assoc]
  have k2 : ∀ X, O * (Oᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hOO, Matrix.one_mul]
  have k4 : Di * (Λ * Di) = 1 := by
    simp only [hDi, hΛ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    have h0 : 0 ≤ μ j := (hA5.2 j).le
    field_simp [hsq j]
    rw [Real.sq_sqrt h0]
  have k5 : ∀ X, Dh * (Di * X) = X := fun X => by
    rw [← Matrix.mul_assoc]
    simp only [hDi, hDh, Matrix.diagonal_mul_diagonal]
    rw [show (fun j => Real.sqrt (μ j) * (1 / Real.sqrt (μ j))) = fun _ => (1 : ℝ) from
      funext fun j => by field_simp [hsq j], Matrix.diagonal_one, Matrix.one_mul]
  have kΛ : Λ * Di = Di * Λ := by
    simp only [hDi, hΛ, Matrix.diagonal_mul_diagonal, mul_comm]
  have kK : Kmat Sig GB = t * (s * (s * t)) := by
    rw [Kmat, ← Matrix.mul_assoc s s, sqrt_mul_sqrt hGB, Matrix.mul_assoc]
  have hspec : sortedEig (Kmat Sig GB) = μ := hadm.2
  have hDit : Diᵀ = Di := by simp [hDi]
  refine ⟨t * (s * (Oᵀ * Di)), ⟨?_, ?_⟩, ?_⟩
  · -- Vᵀ V = 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hDit, ht, hs, sqrt_transpose]
    rw [← hs, ← ht]
    simp only [Matrix.mul_assoc, k1, k2, k4]
  · -- K V = V Λ
    rw [hspec, kK, ← hΛ]
    simp only [Matrix.mul_assoc, k1, k2, kΛ]
  · -- Nlim
    rw [← qmat_sigmaHat]
    have hQ : Qmat Sig GB (t * (s * (Oᵀ * Di))) = O * s := by
      rw [Qmat, hspec, ← hDh]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hDit, ht, hs, sqrt_transpose]
      rw [← hs, ← ht]
      simp only [Matrix.mul_assoc, k5]
      rw [ht, sqrt_mul_inv hSig, Matrix.mul_one]
    rw [hQ, Mhat, Matrix.transpose_mul, hs, sqrt_transpose]
    simp only [Matrix.mul_assoc]

end lemma6

end PCError

end
