import LatentError.Model
import LatentError.Lemmas.Basic

/-!
# The noise array: independence, moments, fourth-moment concentration (Lemma 4)
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

noncomputable section

namespace PCError

/-! ## Elementary inequalities -/

lemma abs_pow_mul_pow_le (x y : ℝ) (a b : ℕ) (h : a + b = 4) :
    |x ^ a * y ^ b| ≤ x ^ 4 + y ^ 4 := by
  have h1 : |x ^ a * y ^ b| ≤ max |x| |y| ^ 4 := by
    rw [abs_mul, abs_pow, abs_pow, ← h, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg x) (le_max_left _ _) a)
      (pow_le_pow_left₀ (abs_nonneg y) (le_max_right _ _) b) (by positivity) (by positivity)
  have hx4 : x ^ 4 = |x| ^ 4 := (Even.pow_abs (by decide) x).symm
  have hy4 : y ^ 4 = |y| ^ 4 := (Even.pow_abs (by decide) y).symm
  have h2 : max |x| |y| ^ 4 ≤ x ^ 4 + y ^ 4 := by
    rw [hx4, hy4]
    rcases max_cases |x| |y| with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;>
      nlinarith [pow_nonneg (abs_nonneg x) 4, pow_nonneg (abs_nonneg y) 4]
  linarith

lemma sq_mul_sq_le (x y : ℝ) : x ^ 2 * y ^ 2 ≤ (x ^ 4 + y ^ 4) / 2 := by
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]

section noise

variable {n : ℕ} {var : ℕ → Fin n → ℝ} {κ4 : ℝ} {Ω : Type} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrability of mixed fourth-order products of `L⁴` functions. -/
lemma integrable_pow_mul_pow_of_memLp4 {f g : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ)
    (hfm : Measurable f) (hgm : Measurable g) (a b : ℕ) (hab : a + b = 4) :
    Integrable (fun ω => f ω ^ a * g ω ^ b) μ := by
  have hf4 : Integrable (fun ω => f ω ^ 4) μ := by
    simpa [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] using
      hf.integrable_norm_pow (p := 4) (by norm_num)
  have hg4 : Integrable (fun ω => g ω ^ 4) μ := by
    simpa [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] using
      hg.integrable_norm_pow (p := 4) (by norm_num)
  refine (hf4.add hg4).mono' ((hfm.pow_const a).mul (hgm.pow_const b)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_pow_mul_pow_le _ _ a b hab

variable (N : NoiseModel n var κ4 Ω μ)
include N

/-! ## Independence -/

lemma NoiseModel.indep_col (l : Fin n) : iIndepFun (fun i => N.Z i l) μ :=
  N.indep.precomp (g := fun i => (i, l)) (fun a b h => by simpa using h)

lemma NoiseModel.indep_row (i : ℕ) : iIndepFun (N.Z i) μ :=
  N.indep.precomp (g := fun l => (i, l)) (fun a b h => by simpa using h)

lemma NoiseModel.measurable_row (i : ℕ) : Measurable (fun ω => fun l => N.Z i l ω) :=
  measurable_pi_iff.2 fun l => N.meas i l

lemma NoiseModel.indep_rows : iIndepFun (fun i ω => fun l => N.Z i l ω) μ := by
  have hσ : iIndepFun (fun (q : (_ : ℕ) × Fin n) ω => N.Z q.1 q.2 ω) μ :=
    N.indep.precomp (g := Equiv.sigmaEquivProd ℕ (Fin n)) (Equiv.injective _)
  have : ∀ i l, IsProbabilityMeasure (μ.map (N.Z i l)) :=
    fun i l => Measure.isProbabilityMeasure_map (N.meas i l).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map N.measurable_row]
  have hmσ : Measurable (fun ω (q : (_ : ℕ) × Fin n) => N.Z q.1 q.2 ω) :=
    measurable_pi_iff.2 fun q => N.meas q.1 q.2
  have e : (fun ω (i : ℕ) => fun l => N.Z i l ω) =
      (MeasurableEquiv.piCurry (fun (_ : ℕ) (_ : Fin n) => ℝ)) ∘
        (fun ω (q : (_ : ℕ) × Fin n) => N.Z q.1 q.2 ω) := by
    ext; rfl
  rw [e, ← Measure.map_map (MeasurableEquiv.measurable _) hmσ,
    (iIndepFun_iff_map_fun_eq_infinitePi_map
      (X := fun (q : (_ : ℕ) × Fin n) ω => N.Z q.1 q.2 ω) (fun q => N.meas q.1 q.2)).1 hσ,
    Measure.infinitePi_map_piCurry (fun i l => μ.map (N.Z i l))]
  congr 1; funext i
  exact ((iIndepFun_iff_map_fun_eq_infinitePi_map (N.meas i)).1 (N.indep_row i)).symm

/-! ## Moments -/

lemma NoiseModel.memLp2 (i : ℕ) (l : Fin n) : MemLp (N.Z i l) 2 μ :=
  (N.memLp4 i l).mono_exponent (by norm_num)

lemma NoiseModel.integrable_pow4 (i : ℕ) (l : Fin n) :
    Integrable (fun ω => N.Z i l ω ^ 4) μ := by
  have := (N.memLp4 i l).integrable_norm_pow (p := 4) (by norm_num)
  simpa [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] using this

lemma NoiseModel.integral_sq (i : ℕ) (l : Fin n) : μ[fun ω => N.Z i l ω ^ 2] = var i l := by
  rw [← N.var_eq i l, variance_of_integral_eq_zero (N.meas i l).aemeasurable (N.mean_zero i l)]

lemma NoiseModel.memLp_sq (i : ℕ) (l : Fin n) : MemLp (fun ω => N.Z i l ω ^ 2) 2 μ := by
  refine (memLp_two_iff_integrable_sq ((N.meas i l).pow_const 2).aestronglyMeasurable).2 ?_
  simpa [← pow_mul] using N.integrable_pow4 i l

lemma NoiseModel.var_nonneg (i : ℕ) (l : Fin n) : 0 ≤ var i l := by
  rw [← N.var_eq]; exact variance_nonneg _ _

lemma NoiseModel.kappa_nonneg (i : ℕ) (l : Fin n) : 0 ≤ κ4 :=
  le_trans (integral_nonneg fun ω => by positivity) (N.fourth_le i l)

lemma NoiseModel.var_sq_le (i : ℕ) (l : Fin n) : var i l ^ 2 ≤ κ4 := by
  have hv := variance_nonneg (fun ω => N.Z i l ω ^ 2) μ
  rw [variance_eq_sub (N.memLp_sq i l)] at hv
  have h4 : μ[(fun ω => N.Z i l ω ^ 2) ^ 2] = μ[fun ω => N.Z i l ω ^ 4] := by
    congr 1; funext ω; simp [← pow_mul]
  rw [h4, N.integral_sq] at hv
  linarith [N.fourth_le i l]

lemma NoiseModel.var_le_sqrt (i : ℕ) (l : Fin n) : var i l ≤ Real.sqrt κ4 :=
  Real.le_sqrt_of_sq_le (N.var_sq_le i l)

lemma NoiseModel.variance_sq_le (i : ℕ) (l : Fin n) :
    variance (fun ω => N.Z i l ω ^ 2) μ ≤ κ4 := by
  refine le_trans (variance_le_expectation_sq ((N.meas i l).pow_const 2).aestronglyMeasurable) ?_
  refine le_trans (le_of_eq ?_) (N.fourth_le i l)
  congr 1; funext ω; simp [← pow_mul]

/-! ## Weighted column sums and their fourth moments -/

/-- `Σ_{i<m} cᵢ Z_{il}`. -/
def NoiseModel.colSum (c : ℕ → ℝ) (l : Fin n) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range m, c i * N.Z i l ω

lemma NoiseModel.measurable_term (c : ℕ → ℝ) (l : Fin n) (i : ℕ) :
    Measurable (fun ω => c i * N.Z i l ω) :=
  (N.meas i l).const_mul _

lemma NoiseModel.measurable_colSum (c : ℕ → ℝ) (l : Fin n) (m : ℕ) :
    Measurable (N.colSum c l m) :=
  Finset.measurable_sum _ fun i _ => N.measurable_term c l i

lemma NoiseModel.memLp4_term (c : ℕ → ℝ) (l : Fin n) (i : ℕ) :
    MemLp (fun ω => c i * N.Z i l ω) 4 μ :=
  (N.memLp4 i l).const_mul _

lemma NoiseModel.memLp4_colSum (c : ℕ → ℝ) (l : Fin n) (m : ℕ) :
    MemLp (N.colSum c l m) 4 μ :=
  memLp_finset_sum _ fun i _ => N.memLp4_term c l i

lemma NoiseModel.integral_term (c : ℕ → ℝ) (l : Fin n) (i : ℕ) :
    μ[fun ω => c i * N.Z i l ω] = 0 := by
  rw [integral_const_mul, N.mean_zero, mul_zero]

lemma NoiseModel.integral_colSum (c : ℕ → ℝ) (l : Fin n) (m : ℕ) :
    μ[N.colSum c l m] = 0 := by
  unfold NoiseModel.colSum
  rw [integral_finset_sum _ fun i _ => (N.memLp4_term c l i).integrable (by norm_num)]
  exact Finset.sum_eq_zero fun i _ => N.integral_term c l i

lemma NoiseModel.indep_colSum (c : ℕ → ℝ) (l : Fin n) (m : ℕ) :
    IndepFun (N.colSum c l m) (fun ω => c m * N.Z m l ω) μ := by
  have hind : iIndepFun (fun i ω => c i * N.Z i l ω) μ :=
    (N.indep_col l).comp (fun i x => c i * x) fun i => measurable_const.mul measurable_id
  have := hind.indepFun_sum_range_succ (N.measurable_term c l) m
  have e : (∑ j ∈ Finset.range m, fun ω => c j * N.Z j l ω) = N.colSum c l m := by
    funext ω; simp [NoiseModel.colSum]
  rwa [e] at this

omit N in
lemma indep_integral_pow_mul {S X : Ω → ℝ} (h : IndepFun S X μ) (hS : Measurable S)
    (hX : Measurable X) (a b : ℕ) :
    μ[fun ω => S ω ^ a * X ω ^ b] = μ[fun ω => S ω ^ a] * μ[fun ω => X ω ^ b] :=
  (h.comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integral_mul_eq_mul_integral
    (hS.pow_const a).aestronglyMeasurable (hX.pow_const b).aestronglyMeasurable

omit N in
lemma integral_pow_mul_pow_expand {S X : Ω → ℝ} (hS : MemLp S 4 μ) (hX : MemLp X 4 μ)
    (hSm : Measurable S) (hXm : Measurable X) :
    μ[fun ω => (S ω + X ω) ^ 4] =
      μ[fun ω => S ω ^ 4 * X ω ^ 0] + 4 * μ[fun ω => S ω ^ 3 * X ω ^ 1] +
        6 * μ[fun ω => S ω ^ 2 * X ω ^ 2] + 4 * μ[fun ω => S ω ^ 1 * X ω ^ 3] +
          μ[fun ω => S ω ^ 0 * X ω ^ 4] := by
  have hi := fun a b h => integrable_pow_mul_pow_of_memLp4 hS hX hSm hXm a b h
  have e : (fun ω => (S ω + X ω) ^ 4) = fun ω =>
      S ω ^ 4 * X ω ^ 0 + 4 * (S ω ^ 3 * X ω ^ 1) + 6 * (S ω ^ 2 * X ω ^ 2) +
        4 * (S ω ^ 1 * X ω ^ 3) + S ω ^ 0 * X ω ^ 4 := by
    funext ω; ring
  rw [e, integral_add, integral_add, integral_add, integral_add, integral_const_mul,
    integral_const_mul, integral_const_mul]
  all_goals first
    | exact hi _ _ rfl
    | exact (hi _ _ rfl).const_mul _
    | exact ((hi 4 0 rfl).add ((hi 3 1 rfl).const_mul _))
    | exact (((hi 4 0 rfl).add ((hi 3 1 rfl).const_mul _)).add ((hi 2 2 rfl).const_mul _))
    | exact ((((hi 4 0 rfl).add ((hi 3 1 rfl).const_mul _)).add
        ((hi 2 2 rfl).const_mul _)).add ((hi 1 3 rfl).const_mul _))

/-- Second and fourth moments of weighted column sums. -/
theorem NoiseModel.colSum_moments (c : ℕ → ℝ) (l : Fin n) (m : ℕ) :
    μ[fun ω => N.colSum c l m ω ^ 2] = ∑ i ∈ Finset.range m, c i ^ 2 * var i l ∧
    μ[fun ω => N.colSum c l m ω ^ 4] ≤ 3 * κ4 * (∑ i ∈ Finset.range m, c i ^ 2) ^ 2 := by
  have hκ : 0 ≤ κ4 := N.kappa_nonneg 0 l
  induction m with
  | zero => simp [NoiseModel.colSum]
  | succ m ih =>
    obtain ⟨ih2, ih4⟩ := ih
    set S := N.colSum c l m
    set X : Ω → ℝ := fun ω => c m * N.Z m l ω
    have hsplit : N.colSum c l (m + 1) = fun ω => S ω + X ω := by
      funext ω; simp [S, X, NoiseModel.colSum, Finset.sum_range_succ]
    have hind := N.indep_colSum c l m
    have hSm := N.measurable_colSum c l m
    have hXm := N.measurable_term c l m
    have hS4 := N.memLp4_colSum c l m
    have hX4 := N.memLp4_term c l m
    have hS1 : μ[fun ω => S ω ^ 1] = 0 := by simpa using N.integral_colSum c l m
    have hX1 : μ[fun ω => X ω ^ 1] = 0 := by simpa using N.integral_term c l m
    have hX2 : μ[fun ω => X ω ^ 2] = c m ^ 2 * var m l := by
      simp only [X, mul_pow]; rw [integral_const_mul, N.integral_sq]
    have hX4' : μ[fun ω => X ω ^ 4] ≤ c m ^ 4 * κ4 := by
      simp only [X, mul_pow]; rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (N.fourth_le m l) (by positivity)
    have hsum : ∑ i ∈ Finset.range (m + 1), c i ^ 2 = (∑ i ∈ Finset.range m, c i ^ 2) + c m ^ 2 :=
      Finset.sum_range_succ _ _
    refine ⟨?_, ?_⟩
    · have hS2m : MemLp S 2 μ := hS4.mono_exponent (by norm_num)
      have hX2m : MemLp X 2 μ := hX4.mono_exponent (by norm_num)
      have hmeanS : μ[S] = 0 := N.integral_colSum c l m
      have hmeanX : μ[X] = 0 := N.integral_term c l m
      have hmeanSX : μ[fun ω => S ω + X ω] = 0 := by
        rw [integral_add (hS2m.integrable one_le_two) (hX2m.integrable one_le_two), hmeanS,
          hmeanX, add_zero]
      have hvadd := ProbabilityTheory.IndepFun.variance_add hS2m hX2m hind
      rw [variance_of_integral_eq_zero hSm.aemeasurable hmeanS,
        variance_of_integral_eq_zero hXm.aemeasurable hmeanX] at hvadd
      have hvSX : Var[S + X; μ] = μ[fun ω => (S ω + X ω) ^ 2] :=
        variance_of_integral_eq_zero (hSm.add hXm).aemeasurable hmeanSX
      rw [hsplit, ← hvSX, hvadd, Finset.sum_range_succ, ih2]
      simpa using hX2
    · rw [hsplit, integral_pow_mul_pow_expand hS4 hX4 hSm hXm,
        indep_integral_pow_mul hind hSm hXm, indep_integral_pow_mul hind hSm hXm,
        indep_integral_pow_mul hind hSm hXm, indep_integral_pow_mul hind hSm hXm,
        indep_integral_pow_mul hind hSm hXm, hS1, hX1, hX2]
      simp only [pow_zero, integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one,
        one_mul, mul_zero, zero_mul, add_zero]
      have hS2 : μ[fun ω => S ω ^ 2] ≤ Real.sqrt κ4 * ∑ i ∈ Finset.range m, c i ^ 2 := by
        rw [ih2, Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => by
          rw [mul_comm (c i ^ 2)]
          exact mul_le_mul_of_nonneg_right (N.var_le_sqrt i l) (sq_nonneg _)
      have hS2nn : 0 ≤ μ[fun ω => S ω ^ 2] := integral_nonneg fun ω => sq_nonneg _
      have hvar : c m ^ 2 * var m l ≤ c m ^ 2 * Real.sqrt κ4 :=
        mul_le_mul_of_nonneg_left (N.var_le_sqrt m l) (sq_nonneg _)
      have hsq : Real.sqrt κ4 * Real.sqrt κ4 = κ4 := Real.mul_self_sqrt hκ
      rw [hsum]
      set T := ∑ i ∈ Finset.range m, c i ^ 2
      have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hsk : 0 ≤ Real.sqrt κ4 := Real.sqrt_nonneg _
      have hvnn : 0 ≤ c m ^ 2 * var m l := mul_nonneg (sq_nonneg _) (N.var_nonneg m l)
      have h6 : μ[fun ω => S ω ^ 2] * (c m ^ 2 * var m l) ≤
          (Real.sqrt κ4 * T) * (c m ^ 2 * Real.sqrt κ4) :=
        mul_le_mul hS2 hvar hvnn (by positivity)
      nlinarith [sq_nonneg (c m), pow_nonneg (sq_nonneg (c m)) 2]

/-! ## Lemma 4 -/

omit N in
/-- Coefficients of a vector of `ℝᵖ`, extended by zero. -/
def extCoef {p : ℕ} (a : EuclideanSpace ℝ (Fin p)) : ℕ → ℝ :=
  fun i => if h : i < p then a ⟨i, h⟩ else 0

lemma NoiseModel.sum_fin_eq_colSum {p : ℕ} (a : EuclideanSpace ℝ (Fin p)) (l : Fin n) (ω : Ω) :
    ∑ i : Fin p, a i * N.Z i l ω = N.colSum (extCoef a) l p ω := by
  rw [NoiseModel.colSum, ← Fin.sum_univ_eq_sum_range (fun i => extCoef a i * N.Z i l ω)]
  congr 1; funext i; simp [extCoef, i.2]

omit N in
lemma sum_extCoef_sq {p : ℕ} (a : EuclideanSpace ℝ (Fin p)) :
    ∑ i ∈ Finset.range p, extCoef a i ^ 2 = ‖a‖ ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => extCoef a i ^ 2), EuclideanSpace.norm_sq_eq]
  congr 1; funext i; simp [extCoef, i.2, Real.norm_eq_abs, sq_abs]

/-- Markov's inequality with the fourth-moment bound. -/
lemma NoiseModel.tail_bound {p : ℕ} (hp : 0 < p) (a : EuclideanSpace ℝ (Fin p)) (ha : ‖a‖ = 1)
    (l : Fin n) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε * Real.sqrt p ≤ |∑ i : Fin p, a i * N.Z i l ω|} ≤
      ENNReal.ofReal (3 * κ4 / (ε ^ 4 * (p : ℝ) ^ 2)) := by
  have hγ : (fun ω => ∑ i : Fin p, a i * N.Z i l ω) = N.colSum (extCoef a) l p :=
    funext (N.sum_fin_eq_colSum a l)
  have h4 := (N.colSum_moments (extCoef a) l p).2
  rw [sum_extCoef_sq, ha, one_pow, one_pow, mul_one] at h4
  have htpos : 0 < ε ^ 4 * (p : ℝ) ^ 2 := by positivity
  have hint : Integrable (fun ω => N.colSum (extCoef a) l p ω ^ 4) μ := by
    simpa [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] using
      (N.memLp4_colSum (extCoef a) l p).integrable_norm_pow (p := 4) (by norm_num)
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => by positivity) hint (ε ^ 4 * (p : ℝ) ^ 2)
  have hsub : {ω | ε * Real.sqrt p ≤ |∑ i : Fin p, a i * N.Z i l ω|} ⊆
      {ω | ε ^ 4 * (p : ℝ) ^ 2 ≤ N.colSum (extCoef a) l p ω ^ 4} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [N.sum_fin_eq_colSum] at hω
    have h0 : 0 ≤ ε * Real.sqrt p := by positivity
    have h1 := pow_le_pow_left₀ h0 hω 4
    have hs : Real.sqrt p ^ 4 = (p : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Nat.cast_nonneg p)]
    rw [mul_pow, hs, Even.pow_abs (by decide)] at h1
    exact h1
  calc μ {ω | ε * Real.sqrt p ≤ |∑ i : Fin p, a i * N.Z i l ω|}
      ≤ μ {ω | ε ^ 4 * (p : ℝ) ^ 2 ≤ N.colSum (extCoef a) l p ω ^ 4} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | ε ^ 4 * (p : ℝ) ^ 2 ≤ N.colSum (extCoef a) l p ω ^ 4}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (3 * κ4 / (ε ^ 4 * (p : ℝ) ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ htpos]
        linarith

/-- **Lemma 4** (specific return concentration). -/
theorem NoiseModel.concentration (a : (p : ℕ) → EuclideanSpace ℝ (Fin p))
    (ha : ∀ᶠ p in atTop, ‖a p‖ = 1) (l : Fin n) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (∑ i : Fin p, a p i * N.Z i l ω) / Real.sqrt p) atTop
      (𝓝 0) := by
  have key : ∀ m : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ p in atTop,
      |(∑ i : Fin p, a p i * N.Z i l ω) / Real.sqrt p| < 1 / ((m : ℝ) + 1) := by
    intro m
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨p0, hp0⟩ := eventually_atTop.1 (ha.and (eventually_gt_atTop 0))
    set s : ℕ → Set Ω := fun p =>
      {ω | 1 / ((m : ℝ) + 1) * Real.sqrt p ≤ |∑ i : Fin p, a p i * N.Z i l ω|}
    set C : ℝ := 3 * κ4 / (1 / ((m : ℝ) + 1)) ^ 4
    have hbound : ∀ p, μ (s p) ≤
        ENNReal.ofReal (C * (1 / (p : ℝ) ^ 2)) + (if p < p0 then 1 else 0) := by
      intro p
      by_cases hp : p < p0
      · rw [if_pos hp]; exact le_add_left prob_le_one
      · rw [if_neg hp, add_zero]
        obtain ⟨hap, hpos⟩ := hp0 p (not_lt.1 hp)
        refine (N.tail_bound hpos (a p) hap l hε).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
        simp only [C]
        field_simp
    have hsum : ∑' p, μ (s p) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
      rw [ENNReal.tsum_add]
      refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
      · have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) (N.kappa_nonneg 0 l))
          (by positivity)
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => mul_nonneg hC (by positivity))
          ((Real.summable_one_div_nat_pow.2 one_lt_two).mul_left C)]
        exact ENNReal.ofReal_ne_top
      · rw [tsum_eq_sum (s := Finset.range p0) (fun p hp => by
          simp only [Finset.mem_range] at hp; simp [hp])]
        exact ENNReal.sum_ne_top.2 fun p _ => by split_ifs <;> simp
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    filter_upwards [hω, eventually_gt_atTop 0] with p hp hp0'
    simp only [s, Set.mem_setOf_eq, not_le] at hp
    have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 (Nat.cast_pos.2 hp0')
    rw [abs_div, abs_of_pos hsp, div_lt_iff₀ hsp]
    linarith
  rw [← ae_all_iff] at key
  filter_upwards [key] with ω hω
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω m] with p hp
  rw [Real.dist_eq, sub_zero]
  exact hp.trans hm

end noise

end PCError

end
