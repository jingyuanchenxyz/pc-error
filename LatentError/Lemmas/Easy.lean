import LatentError.Lemmas.Duality

/-!
# Small leaf lemmas for the bridge to Ono's formalization

Scalar algebra for Theorem 2 / eq. (19), sign invariances, index conversions, and the
padded identity used as filler data for small `p`.  Written as leaf goals for the local
harness (`harness/prove.py --all`); hints are in comments.
-/

open scoped Matrix Topology MatrixOrder
open Filter

noncomputable section

namespace PCError

variable {k n : ℕ}

/-! ## Scalar algebra -/

lemma thm1Limit_eq_one_sub (n : ℕ) (δ2 l s : ℝ) (hδ : 0 < δ2) (hl : 0 ≤ l) :
    thm1Limit n δ2 l s = 1 - ((n : ℝ) * l / ((n : ℝ) * l + δ2)) * (1 - s) := by
  -- hint: unfold thm1Limit; have : 0 < (n:ℝ) * l + δ2 := by positivity; field_simp; ring
  unfold thm1Limit
  have : 0 < (n : ℝ) * l + δ2 := by positivity
  field_simp
  ring

lemma floor_le_thm1Limit (n : ℕ) (δ2 l s : ℝ) (hδ : 0 < δ2) (hl : 0 ≤ l) (hs : 0 ≤ s) :
    δ2 / ((n : ℝ) * l + δ2) ≤ thm1Limit n δ2 l s := by
  unfold thm1Limit
  have h0 : 0 ≤ (n : ℝ) * l := mul_nonneg (Nat.cast_nonneg n) hl
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg h0 (by positivity)) hs)

lemma floor_eq_thm1Limit_iff (n : ℕ) (hn : 0 < n) (δ2 l s : ℝ) (hδ : 0 < δ2) (hl : 0 < l) :
    δ2 / ((n : ℝ) * l + δ2) = thm1Limit n δ2 l s ↔ s = 0 := by
  unfold thm1Limit
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hc : 0 < (n : ℝ) * l / ((n : ℝ) * l + δ2) := by positivity
  constructor
  · intro h
    have h0 : (n : ℝ) * l / ((n : ℝ) * l + δ2) * s = 0 := by linarith
    exact (mul_eq_zero.1 h0).resolve_left hc.ne'
  · rintro rfl
    simp

/-- The in-subspace limit (19) from the total limit (17) and the floor (18). -/
lemma inSubspace_algebra (n : ℕ) (δ2 l s : ℝ) (hδ : 0 < δ2) (hl : 0 < l) (hn : 0 < n) :
    (thm1Limit n δ2 l s - δ2 / ((n : ℝ) * l + δ2)) /
      ((n : ℝ) * l / ((n : ℝ) * l + δ2)) = s := by
  -- hint: unfold thm1Limit; have : 0 < (n:ℝ) * l := by positivity; field_simp; ring
  unfold thm1Limit
  have : 0 < (n : ℝ) * l := by positivity
  field_simp
  ring

lemma sum_floor_pos (hk : 1 ≤ k) (δ2 : ℝ) (hδ : 0 < δ2) (l : Fin k → ℝ) (hl : ∀ j, 0 ≤ l j) :
    0 < ∑ j : Fin k, δ2 / ((n : ℝ) * l j + δ2) := by
  exact Finset.sum_pos (fun j _ => div_pos hδ
    (add_pos_of_nonneg_of_pos (mul_nonneg (Nat.cast_nonneg n) (hl j)) hδ))
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩

/-! ## Sign invariances -/

lemma sinSq_neg_right {m : ℕ} (u v : EuclideanSpace ℝ (Fin m)) : sinSq u (-v) = sinSq u v := by
  -- hint: simp [sinSq]
  simp [sinSq, inner_neg_left, norm_neg]

lemma sinSq_eq_of_eq_or_neg {m : ℕ} {u u' : EuclideanSpace ℝ (Fin m)}
    (h : u' = u ∨ u' = -u) (v : EuclideanSpace ℝ (Fin m)) : sinSq u' v = sinSq u v := by
  -- hint: rcases h with rfl | rfl; rfl; exact sinSq_neg_left u v
  rcases h with rfl | rfl
  · rfl
  · exact sinSq_neg_left u v

lemma projB_mul_signs {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (s : Fin k → ℝ)
    (hs : ∀ j, s j * s j = 1) : projB (b * Matrix.diagonal s) = projB b := by
  -- hint: simp only [projB, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc];
  -- rw [← Matrix.mul_assoc (Matrix.diagonal s), Matrix.diagonal_mul_diagonal]; then show the
  -- diagonal is 1 using hs (Matrix.diagonal_one) and simp
  simp only [projB, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal s), Matrix.diagonal_mul_diagonal]
  simp [hs]

lemma colVec_mul_signs {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (s : Fin k → ℝ) (j : Fin k) :
    colVec (b * Matrix.diagonal s) j = s j • colVec b j := by
  -- hint: exact colVec_mul_diagonal b s j
  exact colVec_mul_diagonal b s j

/-! ## Index conversions -/

lemma sortedEigN_fin {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (j : ℕ) (hj : j < m) :
    sortedEigN A j = sortedEig A ⟨j, hj⟩ := by
  -- hint: simp [sortedEigN, hj]
  simp [sortedEigN, hj]

lemma tendsto_adm_iff {α : Type*} {f : ℕ → α} {l : Filter α} :
    Tendsto (fun P : {p : ℕ // k ≤ p} => f P.1) atTop l ↔ Tendsto f atTop l := by
  -- hint: exact Filter.tendsto_comp_val_Ici_atTop (a := k)
  exact Filter.tendsto_comp_val_Ici_atTop (a := k)

/-! ## The padded identity (filler data for small `p`) -/

/-- `E ∈ ℝ^{p×k}` with `Eᵢⱼ = 1` iff `i = j`. -/
def padId (p k : ℕ) : Matrix (Fin p) (Fin k) ℝ := Matrix.of fun i j => if (i : ℕ) = j then 1 else 0

lemma padId_transpose_mul {p : ℕ} (hkp : k ≤ p) : (padId p k)ᵀ * padId p k = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, padId, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨i, lt_of_lt_of_le i.2 hkp⟩ : Fin p)]
  · by_cases hij : i = j
    · subst hij; simp
    · have h' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [hij, h']
  · intro x _ hx
    have : (x : ℕ) ≠ i := fun h => hx (Fin.ext h)
    simp [this]
  · simp

end PCError

end
