import Mathlib
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.style.commandStart false
set_option linter.style.lambdaSyntax false
set_option linter.style.emptyLine false
set_option linter.flexible false

theorem combinatorial_identity_1 (n i : ℕ) (hi : 1 ≤ i) (hn : 1 ≤ n) : (n.choose i : ℝ) * i = n * (n-1).choose (i-1) := by
  -- First prove the identity in ℕ, then cast to ℝ.
  have h_nat : n.choose i * i = n * (n - 1).choose (i - 1) := by
    -- From the standard identity: (n+1) * choose n k = choose (n+1) (k+1) * (k+1)
    -- instantiate with n-1 and i-1.
    have h := Nat.succ_mul_choose_eq (n - 1) (i - 1)
    -- h : (n - 1).succ * (n - 1).choose (i - 1) =
    --     (n - 1).succ.choose (i - 1).succ * (i - 1).succ
    -- Rewrite using arithmetic on n and i.
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hi' : i - 1 + 1 = i := Nat.sub_add_cancel hi
    -- Turn succs into +1 and then simplify using hn', hi'.
    -- Orient the equality so that the `choose` term with i is on the left.
    have h' := h.symm
    -- Now simplify.
    simpa [Nat.succ_eq_add_one, hn', hi'] using h'
  -- Now move to ℝ using the natural cast.
  have h_real : (n.choose i : ℝ) * (i : ℝ) = (n : ℝ) * ((n - 1).choose (i - 1) : ℝ) := by
    -- Cast the natural-number identity to ℝ and simplify products.
    simpa [Nat.cast_mul] using congrArg (fun k : ℕ => (k : ℝ)) h_nat
  -- Finally, coerce the remaining naturals on both sides to ℝ.
  simpa using h_real

open Real

open Finset in
theorem telescoping_sum_range (a : ℕ → ℝ) (m : ℕ) : ∑ i ∈ range m, (a i - a (i + 1)) = a 0 - a m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    ring

open NNReal in
theorem p_to_nnreal_le_one (p : ℝ) (hp : p ∈ Set.Ioo 0 (1 / 2)) : (⟨p, le_of_lt hp.1⟩ : ℝ≥0) ≤ 1 := by
  have h := hp.2
  have : p < 1 := lt_of_lt_of_le h (by norm_num : (1:ℝ)/2 ≤ 1)
  exact le_of_lt this

open NNReal in
noncomputable def gaussian_core_fun (u : ℝ) : ℝ := 2 * u^(3/2 : ℝ) * Real.exp (1 - u)

open Finset in
noncomputable def midpoint_tail_P (n k : ℕ) (p : ℝ) : ℝ :=
  (1 / 2) * ((∑ i ∈ Finset.Ico k (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)) +
             (∑ i ∈ Finset.Ico (k + 1) (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)))

open Finset in
theorem BA_closed_form (k : ℕ) (hk : 0 < k) :
  let A := (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * k
  let B := Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi)
  B / A = 1 / (2 * ((2 * k).choose k : ℝ) * Real.sqrt Real.pi * Real.sqrt (k : ℝ)) := by
  dsimp
  have hk_real_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h_choose_pos : 0 < ((2 * k).choose k : ℝ) := by
    rw [Nat.cast_pos]
    apply Nat.choose_pos
    omega
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  field_simp
  rw [Real.sq_sqrt hk_real_pos.le]
  ring

open Finset in
theorem correction_term_pos (p : ℝ) (_ : p ∈ Set.Ioo 0 (1 / 2)) (k : ℕ) : 0 ≤ (1 / 2 : ℝ) * ((2 * k).choose k) * (p * (1 - p)).sqrt ^ (2 * k) := by
  apply mul_nonneg
  · apply mul_nonneg
    · norm_num
    · exact Nat.cast_nonneg _
  · exact pow_nonneg (Real.sqrt_nonneg _) _

open ProbabilityTheory in
theorem gaussian_cdf_bounds (x : ℝ) : 0 ≤ cdf (gaussianReal 0 1) x ∧ cdf (gaussianReal 0 1) x ≤ 1 := by
  constructor
  · apply cdf_nonneg
  · apply cdf_le_one

open ProbabilityTheory in
theorem sqrt_pi_le_two: (Real.sqrt (Real.pi) : ℝ) ≤ 2 := by
  have hπ4 : (Real.pi : ℝ) ≤ 4 := le_of_lt Real.pi_lt_four
  have hsqrt : Real.sqrt Real.pi ≤ Real.sqrt 4 := by
    -- use monotonicity of sqrt
    have := Real.sqrt_le_sqrt hπ4
    simpa using this
  -- now show sqrt 4 = 2
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    -- use sqrt_eq_iff_mul_self_eq_of_pos
    have hpos : (0 : ℝ) < 2 := by norm_num
    have h := (Real.sqrt_eq_iff_mul_self_eq_of_pos hpos : Real.sqrt (4 : ℝ) = 2 ↔ 2 * 2 = (4 : ℝ))
    have : 2 * 2 = (4 : ℝ) := by norm_num
    exact (h.mpr this)
  -- combine
  have : Real.sqrt Real.pi ≤ 2 := by
    have := le_trans hsqrt (le_of_eq hsqrt4)
    simpa using this
  exact this

open ProbabilityTheory in
theorem gaussian_cdf_zero_eq_half: ProbabilityTheory.cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  classical
  -- We follow the high-level strategy purely in terms of measures and cdf.
  -- Let μ be the standard Gaussian measure on ℝ with mean 0 and variance 1.
  let μ : MeasureTheory.Measure ℝ := gaussianReal 0 (1 : NNReal)
  -- 1. Symmetry of μ under x ↦ -x.
  have h_symm : μ.map (fun x : ℝ => -x) = μ := by
    -- gaussianReal_map_neg: (gaussianReal μ v).map (-·) = gaussianReal (-μ) v
    have h0 : (gaussianReal 0 (1 : NNReal)).map (fun x : ℝ => -x) = gaussianReal 0 (1 : NNReal) := by
      simpa using
        (ProbabilityTheory.gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
    simpa [μ] using h0
  -- 2. From symmetry, get equality of the measures of Iic 0 and Ici 0.
  have h_half_sets : μ (Set.Iic (0 : ℝ)) = μ (Set.Ici 0) := by
    -- Apply both sides of h_symm to Iic 0 and use map_apply.
    have h := congrArg (fun ν : MeasureTheory.Measure ℝ => ν (Set.Iic (0 : ℝ))) h_symm
    -- Rewrite the left-hand side using map_apply and compute the preimage.
    have h_map :
        μ.map (fun x : ℝ => -x) (Set.Iic (0 : ℝ))
          = μ ((fun x : ℝ => -x) ⁻¹' Set.Iic (0 : ℝ)) := by
      -- map_apply requires measurability of the set.
      have hmeas : MeasurableSet (Set.Iic (0 : ℝ)) := by
        exact (measurableSet_Iic : MeasurableSet (Set.Iic (0 : ℝ)))
      simpa [hmeas] using
        (MeasureTheory.Measure.map_apply (μ := μ) (f := fun x : ℝ => -x)
          (hf := by fun_prop) (hs := hmeas))
    have h_pre : (fun x : ℝ => -x) ⁻¹' Set.Iic (0 : ℝ) = Set.Ici 0 := by
      ext x; simp [Set.preimage, Set.mem_Iic, Set.mem_Ici]
    -- Use these to rewrite h.
    have h' : μ (Set.Ici 0) = μ (Set.Iic (0 : ℝ)) := by
      simpa [h_map, h_pre] using h
    simpa [eq_comm] using h'
  -- 3. The whole space is the union of Iic 0 and Ici 0, and their intersection is {0}.
  have h_union : Set.Iic (0 : ℝ) ∪ Set.Ici 0 = (Set.univ : Set ℝ) := by
    simpa using (Set.Iic_union_Ici (a := (0 : ℝ)))
  have h_inter : Set.Iic (0 : ℝ) ∩ Set.Ici 0 = ({0} : Set ℝ) := by
    have h := (Set.Iic_inter_Ici (a := (0 : ℝ)) (b := (0 : ℝ)))
    -- h : Iic 0 ∩ Ici 0 = Icc 0 0
    simpa [Set.Icc_self] using h
  -- 4. μ is a probability measure and has no atom at 0, so μ {0} = 0.
  have hμ_prob : MeasureTheory.IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have h_noAtoms : MeasureTheory.NoAtoms μ := by
    dsimp [μ]
    have h1 : (1 : NNReal) ≠ 0 := by exact one_ne_zero
    simpa using
      (ProbabilityTheory.noAtoms_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) h1)
  have h_zero : μ ({0} : Set ℝ) = 0 := by
    simpa using (MeasureTheory.measure_singleton (μ := μ) (a := (0 : ℝ)))
  -- 5. Use real-valued measure μ.real and finite additivity on the union Iic 0 ∪ Ici 0.
  have h_add_real :
      μ.real (Set.Iic (0 : ℝ)) + μ.real (Set.Ici 0) = 1 := by
    -- Use the lemma for real-valued measure: measureReal_union_add_inter.
    have h_union_inter :
        μ.real (Set.Iic (0 : ℝ)) + μ.real (Set.Ici 0)
          = μ.real (Set.Iic (0 : ℝ) ∪ Set.Ici 0)
              + μ.real (Set.Iic (0 : ℝ) ∩ Set.Ici 0) := by
      -- Note: the lemma is stated with RHS = 1 + μ.real (s ∩ t), but we can rewrite.
      have h0 :=
        (MeasureTheory.measureReal_union_add_inter (μ := μ)
          (s := Set.Iic (0 : ℝ)) (t := Set.Ici 0)
          (ht := (by
            -- measurability of Ici 0
            exact (measurableSet_Ici : MeasurableSet (Set.Ici (0 : ℝ))))))
      -- h0 : 1 + μ.real (Iic 0 ∩ Ici 0) = μ.real (Iic 0) + μ.real (Ici 0)
      -- Rearrange to the desired form.
      have := h0.symm
      simpa [add_comm, add_left_comm, add_assoc] using this
    -- Simplify the right-hand side using h_union and h_inter, plus values at univ and {0}.
    have h_univ_real : μ.real (Set.univ : Set ℝ) = 1 := by
      -- Since μ is a probability measure, μ univ = 1, and real gives 1.
      have hμ_univ : μ (Set.univ : Set ℝ) = 1 := by
        simpa using (MeasureTheory.IsProbabilityMeasure.measure_univ (μ := μ))
      simp [MeasureTheory.measureReal_def, hμ_univ]
    have h_zero_real : μ.real ({0} : Set ℝ) = 0 := by
      have hμ_zero : μ ({0} : Set ℝ) = 0 := h_zero
      simp [MeasureTheory.measureReal_def, hμ_zero]
    -- Rewrite union and intersection.
    have h_union' : μ.real (Set.Iic (0 : ℝ) ∪ Set.Ici 0) = μ.real (Set.univ : Set ℝ) := by
      simpa [h_union]
    have h_inter' : μ.real (Set.Iic (0 : ℝ) ∩ Set.Ici 0) = μ.real ({0} : Set ℝ) := by
      simpa [h_inter]
    -- Combine everything.
    calc
      μ.real (Set.Iic (0 : ℝ)) + μ.real (Set.Ici 0)
          = μ.real (Set.Iic (0 : ℝ) ∪ Set.Ici 0)
              + μ.real (Set.Iic (0 : ℝ) ∩ Set.Ici 0) := h_union_inter
      _ = μ.real (Set.univ : Set ℝ) + μ.real ({0} : Set ℝ) := by
            simpa [h_union', h_inter']
      _ = 1 := by
            simp [h_univ_real, h_zero_real]
  -- 6. Real-valued equality of Iic 0 and Ici 0.
  have h_Iic_Ici_real : μ.real (Set.Iic (0 : ℝ)) = μ.real (Set.Ici 0) := by
    -- apply ENNReal.toReal to h_half_sets
    have := congrArg ENNReal.toReal h_half_sets
    simpa [MeasureTheory.measureReal_def] using this
  -- 7. From h_add_real and h_Iic_Ici_real, deduce μ.real (Iic 0) = 1/2.
  have h_Iic_val_real : μ.real (Set.Iic (0 : ℝ)) = 1 / 2 := by
    have : μ.real (Set.Iic (0 : ℝ)) + μ.real (Set.Iic (0 : ℝ)) = 1 := by
      simpa [h_Iic_Ici_real, two_mul] using h_add_real
    have h_mul : (2 : ℝ) * μ.real (Set.Iic (0 : ℝ)) = 1 := by
      simpa [two_mul, add_comm] using this
    have := congrArg (fun x : ℝ => (1 / 2 : ℝ) * x) h_mul
    -- Left becomes (1/2)*2*a = a, right is 1/2.
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- 8. Express the cdf at 0 in terms of μ.real (Iic 0).
  have h_cdf : ProbabilityTheory.cdf μ 0 = μ.real (Set.Iic (0 : ℝ)) := by
    simpa using (ProbabilityTheory.cdf_eq_real (μ := μ) 0)
  -- 9. Hence the cdf at 0 is 1/2.
  have h_cdf_val : ProbabilityTheory.cdf μ 0 = 1 / 2 := by
    simpa [h_cdf, h_Iic_val_real]
  -- 10. Rewrite back in terms of `gaussianReal 0 1`.
  simpa [μ] using h_cdf_val

open Set MeasureTheory Filter Topology in
theorem calculus_gap_lemma (f g : ℝ → ℝ) (a b : ℝ) (_ : a < b) (hcont : ContinuousOn (f - g) (Set.Icc a b)) (hdiff_f : DifferentiableOn ℝ f (Set.Ioo a b)) (hdiff_g : DifferentiableOn ℝ g (Set.Ioo a b)) (hderiv : ∀ x ∈ Set.Ioo a b, deriv f x ≤ deriv g x) (hend : f b = g b) : ∀ x ∈ Set.Ico a b, f x ≥ g x := by
  classical
  intro x hx
  have hx_lt : x < b := hx.2
  have hx_cc : x ∈ Icc a b := ⟨hx.1, le_of_lt hx_lt⟩
  -- Define h and inherit continuity / differentiability from f - g.
  set h := fun y ↦ f y - g y with hdef
  have hcont' : ContinuousOn h (Icc a b) := by
    simpa [hdef] using hcont
  have hdiff' : DifferentiableOn ℝ h (Ioo a b) := by
    -- f - g is differentiable on (a,b) since f and g are
    have := hdiff_f.sub hdiff_g
    simpa [hdef] using this
  -- Restrict to [x,b].
  have hsubset₁ : Icc x b ⊆ Icc a b := by
    intro y hy
    exact ⟨le_trans hx.1 hy.1, hy.2⟩
  have hsubset₂ : Ioo x b ⊆ Ioo a b := by
    intro y hy
    exact ⟨lt_of_le_of_lt hx.1 hy.1, hy.2⟩
  have hcont_xb : ContinuousOn h (Icc x b) := hcont'.mono hsubset₁
  have hdiff_xb : DifferentiableOn ℝ h (Ioo x b) := hdiff'.mono hsubset₂
  -- Apply the mean value theorem on [x,b] to h.
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_deriv_eq_slope (f := h) hx_lt hcont_xb hdiff_xb
  -- So deriv h c = (h b - h x) / (b - x) for some c ∈ (x,b).
  have hc_ab : c ∈ Ioo a b := by
    have hc_xb : c ∈ Ioo x b := hc_mem
    exact ⟨lt_of_le_of_lt hx.1 hc_xb.1, hc_xb.2⟩
  -- Relate deriv h c to deriv f c and deriv g c.
  have hf_diff : DifferentiableAt ℝ f c := by
    -- use differentiability of f on (a,b)
    have : c ∈ Ioo a b := hc_ab
    have h_open : IsOpen (Ioo a b) := isOpen_Ioo
    exact (hdiff_f.differentiableAt (Filter.mem_of_superset (IsOpen.mem_nhds h_open this) (by intro y hy; exact hy)))
  have hg_diff : DifferentiableAt ℝ g c := by
    have : c ∈ Ioo a b := hc_ab
    have h_open : IsOpen (Ioo a b) := isOpen_Ioo
    exact (hdiff_g.differentiableAt (Filter.mem_of_superset (IsOpen.mem_nhds h_open this) (by intro y hy; exact hy)))
  have h_deriv_rel : deriv h c = deriv f c - deriv g c := by
    have h_sub : deriv (fun y ↦ f y - g y) c = deriv f c - deriv g c := by
      simpa using (deriv_sub (f := f) (g := g) (x := c) hf_diff hg_diff)
    simpa [hdef] using h_sub
  -- From hderiv we have deriv f c ≤ deriv g c.
  have hfg_le : deriv f c ≤ deriv g c := hderiv c hc_ab
  -- Hence deriv h c ≤ 0.
  have h_deriv_le_zero : deriv h c ≤ 0 := by
    have : deriv f c - deriv g c ≤ 0 := sub_nonpos.mpr hfg_le
    simpa [h_deriv_rel] using this
  -- Rewrite the MVT equality.
  have h_slope_le_zero : (h b - h x) / (b - x) ≤ 0 := by
    simpa [hc_eq] using h_deriv_le_zero
  have hxb_pos : 0 < b - x := sub_pos.mpr hx_lt
  -- Use div_nonpos_iff to deduce h b - h x ≤ 0 from the sign of the slope.
  have hb_sub_hx_le_zero : h b - h x ≤ 0 := by
    have h_cases := (div_nonpos_iff).1 h_slope_le_zero
    have h_not : ¬ b - x ≤ 0 := by exact not_le.mpr hxb_pos
    rcases h_cases with h1 | h2
    · -- first case leads to contradiction with b - x > 0
      exact (h_not h1.2).elim
    · -- second case gives the desired inequality
      exact h2.1
  have hb_le_hx : h b ≤ h x := sub_nonpos.mp hb_sub_hx_le_zero
  -- Endpoint equality f b = g b implies h b = 0.
  have hb_zero : h b = 0 := by
    simp [hdef, hend]
  have hx_ge_zero : 0 ≤ h x := by
    have : h b ≤ h x := hb_le_hx
    simpa [hb_zero] using this
  -- Translate back to f x ≥ g x.
  have hx_ge_zero_fxgx : 0 ≤ f x - g x := by
    simpa [hdef] using hx_ge_zero
  have hx_ge : g x ≤ f x := sub_nonneg.mp hx_ge_zero_fxgx
  exact hx_ge

open Set MeasureTheory Filter Topology in
theorem deriv_gap_algebra_identity (k : ℕ) (hk : 0 < k) (p : ℝ) :
  let s : ℝ := p * (1 - p);
  (p^(k - 1) * (1 - p)^k) - (1 / 2 : ℝ) * (1 - 2 * p) * s^(k - 1) =
    (1 / 2 : ℝ) * s^(k - 1) := by
  intro s
  have h_split : (1 - p)^k = (1 - p)^(k - 1) * (1 - p) := by
    nth_rewrite 1 [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  rw [h_split]
  dsimp [s]
  rw [mul_pow]
  ring

open Set MeasureTheory Filter Topology in
theorem binomial_tail_prob_arg_eq (k : ℕ) (μ scale : ℝ) (h_scale : scale ≠ 0) : μ + ((k - 1 - μ) / scale) * scale = (k : ℝ) - 1 := by
  field_simp
  ring

open Finset in
noncomputable def midpoint_tail_polynomial (n k : ℕ) (p : ℝ) : ℝ :=
  (1 / 2) * ((∑ i ∈ Finset.Ico k (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)) +
             (∑ i ∈ Finset.Ico (k + 1) (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)))

open ProbabilityTheory in
theorem gaussianPDFReal_std (x : ℝ) : ProbabilityTheory.gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x^2) / 2) := by
  simp [ProbabilityTheory.gaussianPDFReal, pow_two]

open Finset in
noncomputable def midpoint_tail_Q (n k : ℕ) (p : ℝ) : ℝ :=
  (1 / 2) * ((∑ i ∈ Finset.Ico k (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)) +
             (∑ i ∈ Finset.Ico (k + 1) (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)))

open Filter Topology Set in
theorem eventually_Ioo_of_nhdsWithin_Ioi (c : ℝ) (hc : 0 < c) : Filter.Eventually (fun p => p ∈ Set.Ioo 0 c) (nhdsWithin 0 (Set.Ioi 0)) := by
  -- Reinterpret the "eventually" statement as membership of a set in the filter.
  -- `∀ᶠ p in l, p ∈ s` is equivalent to `s ∈ l`.
  have hmem : Set.Ioo (0 : ℝ) c ∈ nhdsWithin 0 (Set.Ioi 0) := by
    -- The filter `nhdsWithin 0 (Ioi 0)` is the right-neighborhood filter `𝓝[>] 0`,
    -- and `Ioo_mem_nhdsGT` says that `(0, c)` is a member of this filter when `0 < c`.
    simpa using (Ioo_mem_nhdsGT (a := (0 : ℝ)) (b := c) hc)
  -- Turn this membership into the desired `Eventually` statement.
  -- Use `Filter.eventually_mem_set : (∀ᶠ x in l, x ∈ s) ↔ s ∈ l`.
  exact (Filter.eventually_mem_set).2 hmem

open Filter Topology Set in
noncomputable def telescoping_term (n i : ℕ) (x : ℝ) : ℝ := n * ((n-1).choose i) * x ^ i * (1 - x) ^ (n - 1 - i)

open Filter Topology Set in
theorem sigma_bound (p : ℝ) (hp : p ∈ Set.Ioo 0 (1 / 2)) : (p * (1 - p)).sqrt ≤ 1 / 2 := by
  rcases hp with ⟨h₀, h₁⟩
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith

open Filter Topology Set in
theorem central_tail_algebra (n : ℕ) (hn : 0 < n) (L C U : ℝ)
  (hLU : L = U) (htotal : L + C + U = (2 : ℝ) ^ n) :
  C + U = (2 : ℝ) ^ (n - 1) + C / 2 := by
  have h1 : U + C + U = (2 : ℝ) ^ n := by
    simpa [hLU, add_comm, add_left_comm, add_assoc] using htotal
  have h1b : 2 * U + C = (2 : ℝ) ^ n := by
    calc
      2 * U + C = U + C + U := by ring
      _ = (2 : ℝ) ^ n := h1
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    have : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
      simpa [hn1] using (pow_succ (2 : ℝ) (n - 1))
    simpa [mul_comm] using this
  have h2 : 2 * (U + C / 2) = 2 * (2 : ℝ) ^ (n - 1) := by
    calc
      2 * (U + C / 2)
          = 2 * U + C := by ring
      _ = (2 : ℝ) ^ n := h1b
      _ = 2 * (2 : ℝ) ^ (n - 1) := hpow
  have hUC : U + C / 2 = (2 : ℝ) ^ (n - 1) := by
    have hz : (2 : ℝ) ≠ 0 := two_ne_zero
    exact mul_left_cancel₀ hz h2
  have hsplit : U + C = (U + C / 2) + C / 2 := by
    ring
  have hfinal : U + C = (2 : ℝ) ^ (n - 1) + C / 2 := by
    calc
      U + C = (U + C / 2) + C / 2 := hsplit
      _ = (2 : ℝ) ^ (n - 1) + C / 2 := by
        simpa [hUC, add_comm, add_left_comm, add_assoc]
  simpa [add_comm, add_left_comm, add_assoc] using hfinal

open Filter Topology Set in
theorem central_binom_bound (k : ℕ) : (2 * k).choose k ≤ 4 ^ k := by
  -- We bound (2k choose k) by the middle binomial coefficient of the next row,
  -- then use the standard inequality on that middle coefficient.
  have h₁ : (2 * k).choose k ≤ (2 * k + 1).choose k := by
    simpa using (Nat.choose_le_succ (2 * k) k)
  have h₂ : (2 * k + 1).choose k ≤ 4 ^ k := Nat.choose_middle_le_pow k
  exact le_trans h₁ h₂

open Filter Topology Set in
theorem gaussian_limit_zero_helper (k c : ℝ) (hc : 0 < c) : Filter.Tendsto (fun x => x ^ k * Real.exp (-c * x)) Filter.atTop (nhds 0) := by
  -- We can use the general lemma about the limit of x^s * exp(-b*x)
  simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k c hc

open Filter Topology Set in
noncomputable def ramp_function (a b x : ℝ) : ℝ :=
  if x ≤ a then (0 : ℝ) else if b ≤ x then (1 : ℝ) else (x - a) / (b - a)

open Filter Topology Set in
theorem hasDerivAt_z_div_sqrt (x : ℝ) : HasDerivAt (fun t : ℝ => t / Real.sqrt (t^2 + 1)) (1 / (x^2 + 1) ^ (3/2 : ℝ)) x := by
  have h_pos : 0 < x^2 + 1 := by nlinarith
  have h_ne : x^2 + 1 ≠ 0 := ne_of_gt h_pos

  -- Helper 1: Derivative of s(t) = t^2 + 1
  have h1 : HasDerivAt (fun t => t^2 + 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const 1

  -- Helper 2: Derivative of s(t)^(-1/2)
  have h2 : HasDerivAt (fun t => (t^2 + 1) ^ (-(1/2 : ℝ))) (-x * (x^2 + 1) ^ (-(3/2 : ℝ))) x := by
    have := HasDerivAt.rpow_const (p := -(1/2 : ℝ)) h1 (Or.inl h_ne)
    convert this using 1
    -- 2 * x * (-1/2) * (x^2 + 1)^(-3/2)
    field_simp
    ring_nf

  -- Helper 3: Derivative of t * s(t)^(-1/2)
  have h3 : HasDerivAt (fun t => t * (t^2 + 1) ^ (-(1/2 : ℝ))) ((x^2 + 1) ^ (-(3/2 : ℝ))) x := by
    have := HasDerivAt.mul (hasDerivAt_id x) h2
    convert this using 1
    simp only [id_eq, one_mul]

    -- Need: (x^2 + 1)^(-1/2) + x * (-x * (x^2 + 1)^(-3/2)) = (x^2 + 1)^(-3/2)
    -- Factor (x^2 + 1)^(-3/2)
    have aux : (x^2 + 1 : ℝ) * (x^2 + 1) ^ (-(3/2 : ℝ)) = (x^2 + 1) ^ (-(1/2 : ℝ)) := by
      rw [mul_comm, ← Real.rpow_add_one h_ne]
      norm_num

    rw [← aux]
    ring

  -- Helper 4: Rewrite original function
  have h_eq : (fun t => t / Real.sqrt (t^2 + 1)) = (fun t => t * (t^2 + 1) ^ (-(1/2 : ℝ))) := by
    ext t
    have ht_pos : 0 < t^2 + 1 := by nlinarith
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_neg (le_of_lt ht_pos)]

  -- Helper 5: Rewrite target value
  have h_val : (x^2 + 1) ^ (-(3/2 : ℝ)) = 1 / (x^2 + 1) ^ (3/2 : ℝ) := by
    rw [Real.rpow_neg (le_of_lt h_pos), one_div]

  rw [h_eq, ← h_val]
  exact h3

open ProbabilityTheory in
theorem pmf_map_coe_eq (n : ℕ) (P : PMF (Fin (n + 1))) : P.map (fun i : Fin (n + 1) => (i : ℝ)) = (P.map (fun i : Fin (n + 1) => (i : ℕ))).map (fun i : ℕ => (i : ℝ)) := by
  rw [PMF.map_comp]
  rfl

open ProbabilityTheory in
theorem combinatorial_identity_2 (n i : ℕ) (hi : i ≤ n) (hn : 1 ≤ n) : (n.choose i : ℝ) * (n - i) = n * (n-1).choose i := by
  rw [← Nat.cast_sub hi]
  norm_cast
  have h := Nat.choose_mul_succ_eq (n - 1) i
  have h_succ : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [h_succ] at h
  rw [mul_comm] at h
  exact h.symm

open ProbabilityTheory in
theorem log_one_div_two_mul_four_pow (k : ℕ) :
  -(k + 1/2 : ℝ) * Real.log 4 = Real.log (1 / (2 * (4 : ℝ) ^ k)) := by
  -- first, rewrite the logarithm on the right-hand side
  have hR : Real.log (1 / (2 * (4 : ℝ) ^ k)) =
      - (Real.log 2 + (k : ℝ) * Real.log 4) := by
    -- log of reciprocal
    have h_mul : Real.log (2 * (4 : ℝ) ^ k) =
        Real.log 2 + Real.log ((4 : ℝ) ^ k) := by
      have hne2 : (2 : ℝ) ≠ 0 := by norm_num
      have hne4 : (4 : ℝ) ≠ 0 := by norm_num
      have hne4pow : (4 : ℝ) ^ k ≠ 0 := pow_ne_zero _ hne4
      simpa using
        (Real.log_mul (x := (2 : ℝ)) (y := (4 : ℝ) ^ k) hne2 hne4pow)
    have h_pow : Real.log ((4 : ℝ) ^ k) = (k : ℝ) * Real.log 4 := by
      simpa using (Real.log_pow (4 : ℝ) k)
    calc
      Real.log (1 / (2 * (4 : ℝ) ^ k))
          = Real.log ((2 * (4 : ℝ) ^ k)⁻¹) := by
              simp [one_div]
      _   = - Real.log (2 * (4 : ℝ) ^ k) := by
              simpa using
                (Real.log_inv (2 * (4 : ℝ) ^ k))
      _   = - (Real.log 2 + Real.log ((4 : ℝ) ^ k)) := by
              simp [h_mul]
      _   = - (Real.log 2 + (k : ℝ) * Real.log 4) := by
              simp [h_pow]
  -- next, express (1/2) * log 4 as log 2
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    have hpow : (2 : ℝ) ^ 2 = (4 : ℝ) := by norm_num
    simpa [hpow] using h
  have hlog2eq : (1 / 2 : ℝ) * Real.log 4 = Real.log 2 := by
    calc
      (1 / 2 : ℝ) * Real.log 4
          = (1 / 2 : ℝ) * (2 * Real.log 2) := by
              simpa [hlog4]
      _   = ((1 / 2 : ℝ) * 2) * Real.log 2 := by
              ac_rfl
      _   = (1 : ℝ) * Real.log 2 := by
              have : (1 / 2 : ℝ) * 2 = (1 : ℝ) := by norm_num
              simpa [this]
      _   = Real.log 2 := by simp
  -- compute (k + 1/2) * log 4 in terms of log 2 and k * log 4
  have hL0 : (k + 1/2 : ℝ) * Real.log 4 =
      Real.log 2 + (k : ℝ) * Real.log 4 := by
    calc
      (k + 1/2 : ℝ) * Real.log 4
          = (k : ℝ) * Real.log 4 + (1 / 2 : ℝ) * Real.log 4 := by
              simpa using
                (add_mul (k : ℝ) (1 / 2 : ℝ) (Real.log 4))
      _   = (k : ℝ) * Real.log 4 + Real.log 2 := by
              -- use hlog2eq on the second term
              have := hlog2eq
              simpa using
                congrArg (fun t => (k : ℝ) * Real.log 4 + t) this
      _   = Real.log 2 + (k : ℝ) * Real.log 4 := by
              simpa [add_comm, add_left_comm, add_assoc]
  have hL1 : - ((k + 1/2 : ℝ) * Real.log 4) =
      - (Real.log 2 + (k : ℝ) * Real.log 4) := by
    simpa using congrArg Neg.neg hL0
  -- finish by comparing both sides to the common expression
  calc
    -(k + 1/2 : ℝ) * Real.log 4
        = - ((k + 1/2 : ℝ) * Real.log 4) := by
              simpa using (neg_mul (k + 1/2 : ℝ) (Real.log 4))
    _   = - (Real.log 2 + (k : ℝ) * Real.log 4) := hL1
    _   = Real.log (1 / (2 * (4 : ℝ) ^ k)) := by
            exact hR.symm

open ProbabilityTheory in
theorem central_binom_sq_eq_wallis (k : ℕ) : ((2 * k).choose k : ℝ) ^ 2 = (4 : ℝ) ^ (2 * k) / (Real.Wallis.W k * (2 * k + 1)) := by
  classical
  -- Abbreviations for convenience
  let A : ℝ := (Nat.factorial (2 * k) : ℝ) ^ 2
  let B : ℝ := (Nat.factorial k : ℝ) ^ 4
  let C : ℝ := (2 : ℝ) ^ (4 * k)
  let E : ℝ := (2 * k + 1 : ℝ)
  -- Step 1: express the central binomial coefficient via factorials
  have h_le : k ≤ 2 * k := by omega
  have h_sub : 2 * k - k = k := by omega
  have h_choose : ((2 * k).choose k : ℝ)
      = (Nat.factorial (2 * k) : ℝ) /
          ((Nat.factorial k : ℝ) * Nat.factorial (2 * k - k)) := by
    simpa [Nat.cast_choose (K := ℝ) h_le, Nat.cast_mul, Nat.cast_ofNat]
  have h_choose' : ((2 * k).choose k : ℝ)
      = (Nat.factorial (2 * k) : ℝ) /
          ((Nat.factorial k : ℝ) * Nat.factorial k) := by
    simpa [h_choose, h_sub]
  have h_choose_sq' : ((2 * k).choose k : ℝ) ^ 2
      = ((Nat.factorial (2 * k) : ℝ) /
          ((Nat.factorial k : ℝ) * Nat.factorial k)) ^ 2 := by
    simpa [h_choose']
  have h_choose_sq : ((2 * k).choose k : ℝ) ^ 2 = A / B := by
    have : ((Nat.factorial (2 * k) : ℝ) /
              ((Nat.factorial k : ℝ) * Nat.factorial k)) ^ 2
        = (Nat.factorial (2 * k) : ℝ) ^ 2 / (Nat.factorial k : ℝ) ^ 4 := by
      field_simp
    have : ((2 * k).choose k : ℝ) ^ 2
        = (Nat.factorial (2 * k) : ℝ) ^ 2 / (Nat.factorial k : ℝ) ^ 4 := by
      simpa [h_choose_sq'] using this
    simpa [A, B] using this
  -- Step 2: Wallis' product in factorial form
  have hW : Real.Wallis.W k
      = (2 : ℝ) ^ (4 * k) * (Nat.factorial k : ℝ) ^ 4 /
          ((Nat.factorial (2 * k) : ℝ) ^ 2 * (2 * k + 1)) :=
    Real.Wallis.W_eq_factorial_ratio k
  have hW' : Real.Wallis.W k = C * B / (A * E) := by
    simpa [A, B, C, E, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
      using hW
  -- Nonvanishing of A, B, E, and W k
  have hB_ne : B ≠ 0 := by
    have : (Nat.factorial k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero k)
    exact pow_ne_zero 4 this
  have hA_ne : A ≠ 0 := by
    have : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero (2 * k))
    exact pow_ne_zero 2 this
  have hE_pos : (0 : ℝ) < E := by
    have : (0 : ℕ) < 2 * k + 1 := Nat.succ_pos _
    have : (0 : ℝ) < (2 * k + 1 : ℝ) := by exact_mod_cast this
    simpa [E] using this
  have hE_ne : E ≠ 0 := ne_of_gt hE_pos
  have hW_ne : (Real.Wallis.W k) ≠ 0 := ne_of_gt (Real.Wallis.W_pos k)
  -- Step 3: derive A / B = C / (W k * E) from hW'
  -- First, use eq_div_iff on hW' to clear the denominator A * E
  have hAE_ne : (A * E : ℝ) ≠ 0 := mul_ne_zero hA_ne hE_ne
  have h_cross₁ : Real.Wallis.W k * (A * E) = C * B :=
    (eq_div_iff hAE_ne).mp hW'
  have h_cross : A * (Real.Wallis.W k * E) = C * B := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_cross₁
  -- Use eq_div_iff to solve for A and then div_eq_iff to obtain the ratio
  have hWE_ne : (Real.Wallis.W k * E : ℝ) ≠ 0 := mul_ne_zero hW_ne hE_ne
  have hA_eq : A = C * B / (Real.Wallis.W k * E) :=
    (eq_div_iff hWE_ne).2 h_cross
  have h_ratio : A / B = C / (Real.Wallis.W k * E) := by
    have hB_ne' : (B : ℝ) ≠ 0 := hB_ne
    apply (div_eq_iff hB_ne').2
    -- We need to show: A = C / (W k * E) * B
    calc
      A = C * B / (Real.Wallis.W k * E) := hA_eq
      _ = (C / (Real.Wallis.W k * E)) * B := by
            -- Rearrange using commutativity and associativity
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  -- Step 4: rewrite C as 4^(2k)
  have h4 : C = (4 : ℝ) ^ (2 * k) := by
    have h2 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    have h4' : (4 : ℝ) ^ (2 * k) = C := by
      have h4k : (2 * (2 * k) : ℕ) = 4 * k := by omega
      calc
        (4 : ℝ) ^ (2 * k)
            = ((2 : ℝ) ^ 2) ^ (2 * k) := by simpa [h2]
        _ = (2 : ℝ) ^ (2 * (2 * k)) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (pow_mul (2 : ℝ) 2 (2 * k)).symm
        _ = (2 : ℝ) ^ (4 * k) := by simpa [h4k]
        _ = C := rfl
    exact h4'.symm
  -- Step 5: put everything together
  calc
    ((2 * k).choose k : ℝ) ^ 2
        = A / B := h_choose_sq
    _ = C / (Real.Wallis.W k * E) := h_ratio
    _ = (4 : ℝ) ^ (2 * k) / (Real.Wallis.W k * (2 * k + 1)) := by
          simpa [A, B, C, E, h4, mul_comm, mul_left_comm, mul_assoc]

open ProbabilityTheory in
theorem deriv_function_A_raw_simplify (p : ℝ) (hp : 0 < p ∧ p < 1) : let s := p * (1 - p); let num := (1 / 2 - p) * Real.sqrt 2; let den := Real.sqrt s; let num_deriv := -Real.sqrt 2; let den_deriv := (1 - 2 * p) / (2 * Real.sqrt s); (num_deriv * den - num * den_deriv) / den ^ 2 = -Real.sqrt 2 / (4 * s ^ (3 / 2 : ℝ)) := by
  intro s num den num_deriv den_deriv
  dsimp only [s, num, den, num_deriv, den_deriv]

  have hs_pos : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hs_ne : p * (1 - p) ≠ 0 := ne_of_gt hs_pos
  have hsqrt_pos : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr hs_pos
  have hsqrt_ne : Real.sqrt (p * (1 - p)) ≠ 0 := ne_of_gt hsqrt_pos

  -- Simplify den^2
  have h_den_sq : Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) :=
    Real.sq_sqrt (le_of_lt hs_pos)
  rw [h_den_sq]

  -- Simplify the numerator of the fraction
  have h_num :
      (-Real.sqrt 2) * Real.sqrt (p * (1 - p)) -
          ((1 / 2 - p) * Real.sqrt 2) *
            ((1 - 2 * p) / (2 * Real.sqrt (p * (1 - p)))) =
        -Real.sqrt 2 / (4 * Real.sqrt (p * (1 - p))) := by
    -- Multiply by 4 * sqrt s to clear denominators
    rw [eq_div_iff (mul_ne_zero (by norm_num) hsqrt_ne)]
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt (le_of_lt hs_pos)]
    ring

  rw [h_num]

  -- Now we have (-√2 / (4√s)) / s = -√2 / (4 * s^(3/2))
  rw [div_div]
  congr 1
  -- Target: 4 * √s * s = 4 * s^(3/2)
  rw [mul_assoc, mul_comm (Real.sqrt (p * (1 - p))), mul_assoc]
  congr 1
  -- Target: s * √s = s^(3/2)
  have hs_nonneg : 0 ≤ p * (1 - p) := le_of_lt hs_pos
  have h_sqrt :
      Real.sqrt (p * (1 - p)) =
        (p * (1 - p)) ^ (1 / 2 : ℝ) := by
    simpa [Real.sqrt_eq_rpow, hs_nonneg]
  have h_final' :
      (p * (1 - p)) * Real.sqrt (p * (1 - p)) =
        (p * (1 - p)) ^ (3 / 2 : ℝ) := by
    calc
      (p * (1 - p)) * Real.sqrt (p * (1 - p))
          = (p * (1 - p)) * (p * (1 - p)) ^ (1 / 2 : ℝ) := by
              simpa [h_sqrt]
      _ = (p * (1 - p)) ^ (1 : ℝ) *
            (p * (1 - p)) ^ (1 / 2 : ℝ) := by
              simpa [Real.rpow_one]
      _ = (p * (1 - p)) ^ (1 + 1 / 2 : ℝ) := by
            -- use rpow_add for positive base
            have hpos : 0 < p * (1 - p) := hs_pos
            simpa [add_comm, add_left_comm, add_assoc] using
              (Real.rpow_add hpos (1 : ℝ) (1 / 2 : ℝ)).symm
      _ = (p * (1 - p)) ^ (3 / 2 : ℝ) := by
            norm_num
  -- Adjust associativity to match the current goal shape
  have h_final :
      p * ((1 - p) * Real.sqrt (p * (1 - p))) =
        (p * (1 - p)) ^ (3 / 2 : ℝ) := by
    simpa [mul_assoc] using h_final'
  exact h_final

open ProbabilityTheory in
theorem gaussian_u_bounds (s : ℝ) (hs : s ∈ Set.Icc (3/16 : ℝ) (1/4 : ℝ)) : 1 ≤ (1 / (4 * s)) ∧ (1 / (4 * s)) ≤ (4 / 3 : ℝ) := by
  rcases hs with ⟨hs₁, hs₂⟩
  have hs_pos : 0 < s := by
    have : (0 : ℝ) < 3/16 := by norm_num
    exact lt_of_lt_of_le this hs₁
  have h4s_pos : 0 < 4 * s := by
    have : (0 : ℝ) < (4 : ℝ) := by norm_num
    have := mul_pos this hs_pos
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hs₂' : 4 * s ≤ 1 := by
    have h4_nonneg : (0 : ℝ) ≤ 4 := by norm_num
    have := mul_le_mul_of_nonneg_left hs₂ h4_nonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hs₁' : 3/4 ≤ 4 * s := by
    have h4_nonneg : (0 : ℝ) ≤ 4 := by norm_num
    have := mul_le_mul_of_nonneg_left hs₁ h4_nonneg
    have hcalc : (4 : ℝ) * (3/16 : ℝ) = (3/4 : ℝ) := by norm_num
    simpa [mul_comm, mul_left_comm, mul_assoc, hcalc] using this
  have h1 : 1 ≤ 1 / (4 * s) := by
    have := (one_le_inv₀ h4s_pos).2 hs₂'
    simpa [one_div] using this
  have h2 : 1 / (4 * s) ≤ 4 / 3 := by
    have h' : (4 * s)⁻¹ ≤ (3/4 : ℝ)⁻¹ := by
      -- using order-reversing property of inversion
      have : (3/4 : ℝ) ≤ 4 * s := hs₁'
      have hpos34 : (0 : ℝ) < (3/4 : ℝ) := by norm_num
      have := (inv_le_inv₀ h4s_pos hpos34).2 this
      simpa using this
    have : (1 / (4 * s)) ≤ 4 / 3 := by
      simpa [one_div] using h'
    exact this
  exact And.intro h1 h2

open ProbabilityTheory ENNReal Set in
theorem toMeasure_Iic_coe_sub_one (p : PMF ℕ) (k : ℕ) :
  (p.map (fun i : ℕ => (i : ℝ))).toMeasure (Set.Iic ((k : ℝ) - 1)) =
    p.toMeasure {i : ℕ | i < k} := by
  rw [PMF.toMeasure_map_apply]
  · congr 1
    ext i
    simp only [mem_preimage, mem_Iic, mem_setOf_eq]
    rw [le_sub_iff_add_le]
    norm_cast
  · exact measurable_from_top
  · exact measurableSet_Iic

open ProbabilityTheory ENNReal Set in
noncomputable def function_A (x : ℝ) : ℝ := (1 / 2 - x) * Real.sqrt 2 / Real.sqrt (x * (1 - x))

open Finset in
noncomputable def midpoint_tail_poly (n k : ℕ) (p : ℝ) : ℝ :=
  (1 / 2) * ((∑ i ∈ Finset.Ico k (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)) +
             (∑ i ∈ Finset.Ico (k + 1) (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)))

open Finset in
theorem wallis_inequality_for_binom (k : ℕ) (hk : 0 < k) : Real.pi * k ≤ Real.Wallis.W k * (2 * k + 1) := by
  have h := Real.Wallis.le_W k
  have h_pos : 0 ≤ (2 : ℝ) * k + 1 := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h h_pos)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  field_simp
  ring_nf
  linarith

open Finset in
theorem pow_sqrt_sq_eq (k : ℕ) (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x) ^ (2 * k) = x ^ k := by
  rw [pow_mul, Real.sq_sqrt hx]

open Finset in
theorem choose_even_tails_equal_nat (k : ℕ) (hk : 0 < k) :
  let n := 2 * k;
  ∑ i ∈ Finset.Icc 0 (k - 1), Nat.choose n i
    = ∑ i ∈ Finset.Icc (k + 1) n, Nat.choose n i := by
  classical
  -- Unfold the let-bound `n` in the goal.
  change
    ∑ i ∈ Finset.Icc 0 (k - 1), Nat.choose (2 * k) i
      = ∑ i ∈ Finset.Icc (k + 1) (2 * k), Nat.choose (2 * k) i
  -- Rewrite the closed intervals as half-open intervals `[0, k)` and `[k+1, 2k+1)`.
  have h_left : Finset.Icc (0 : ℕ) (k - 1) = Finset.Ico 0 k := by
    -- For naturals, `[0, k-1]` and `[0, k)` have the same elements.
    ext i; constructor
    · intro hi
      have : 0 ≤ i ∧ i ≤ k - 1 := (Finset.mem_Icc.mp hi)
      have hi0 : 0 ≤ i := this.1
      have hik1 : i ≤ k - 1 := this.2
      have hik : i < k :=
        Nat.lt_of_le_of_lt hik1 (Nat.sub_lt (Nat.succ_le_of_lt hk) (by decide))
      exact Finset.mem_Ico.mpr ⟨hi0, hik⟩
    · intro hi
      have : 0 ≤ i ∧ i < k := (Finset.mem_Ico.mp hi)
      have hi0 : 0 ≤ i := this.1
      have hik : i < k := this.2
      have hik1 : i ≤ k - 1 := Nat.le_pred_of_lt hik
      exact Finset.mem_Icc.mpr ⟨hi0, hik1⟩
  have h_right : Finset.Icc (k + 1) (2 * k) = Finset.Ico (k + 1) (2 * k + 1) := by
    -- Similarly, `[k+1, 2k]` and `[k+1, 2k+1)` coincide on ℕ.
    ext i; constructor
    · intro hi
      have : k + 1 ≤ i ∧ i ≤ 2 * k := (Finset.mem_Icc.mp hi)
      have hik1 : k + 1 ≤ i := this.1
      have hi2k : i ≤ 2 * k := this.2
      have hi_lt : i < 2 * k + 1 := lt_of_le_of_lt hi2k (Nat.lt_succ_self _)
      exact Finset.mem_Ico.mpr ⟨hik1, hi_lt⟩
    · intro hi
      have : k + 1 ≤ i ∧ i < 2 * k + 1 := (Finset.mem_Ico.mp hi)
      have hik1 : k + 1 ≤ i := this.1
      have hi_lt : i < 2 * k + 1 := this.2
      have hi2k : i ≤ 2 * k := Nat.le_of_lt_succ hi_lt
      exact Finset.mem_Icc.mpr ⟨hik1, hi2k⟩
  -- Restate the goal with these `Ico` intervals.
  have h_goal :
      (∑ i ∈ Finset.Ico 0 k, Nat.choose (2 * k) i)
        = ∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), Nat.choose (2 * k) i := by
    -- First use symmetry `choose_symm` to rewrite the left sum.
    have h_symm :
        (∑ i ∈ Finset.Ico 0 k, Nat.choose (2 * k) i)
          = ∑ i ∈ Finset.Ico 0 k, Nat.choose (2 * k) (2 * k - i) := by
      refine Finset.sum_congr rfl ?hterm
      intro i hi
      -- From `i ∈ Ico 0 k` we get `i ≤ 2k`.
      have hiIco : 0 ≤ i ∧ i < k := Finset.mem_Ico.mp hi
      have hi_le_2k : i ≤ 2 * k :=
        le_trans (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hiIco.2))
          (by
            have hk_ge1 : 1 ≤ k := hk
            have : k ≤ 2 * k := by
              calc
                k = 1 * k := by simp
                _ ≤ 2 * k := by
                  have : 1 ≤ 2 := by decide
                  exact Nat.mul_le_mul_right _ this
            exact this)
      -- `Nat.choose_symm` gives `choose (2k) (2k - i) = choose (2k) i`.
      have h := Nat.choose_symm (n := 2 * k) (k := i) hi_le_2k
      simpa using h.symm
    -- Now apply the reflection lemma `sum_Ico_reflect`.
    have h_reflect :=
      Finset.sum_Ico_reflect
        (f := fun j => Nat.choose (2 * k) j)
        (k := 0)
        (m := k)
        (n := 2 * k)
        (by
          -- We need `m ≤ n + 1`, i.e. `k ≤ 2k + 1`.
          have hk_ge1 : 1 ≤ k := hk
          have : k ≤ 2 * k := by
            calc
              k = 1 * k := by simp
              _ ≤ 2 * k := by
                have : 1 ≤ 2 := by decide
                exact Nat.mul_le_mul_right _ this
          exact le_trans this (Nat.le_succ _))
    -- Specialize and simplify the statement of `sum_Ico_reflect`.
    have h_reflect' :
        (∑ i ∈ Finset.Ico 0 k, Nat.choose (2 * k) (2 * k - i))
          = ∑ i ∈ Finset.Ico (2 * k + 1 - k) (2 * k + 1), Nat.choose (2 * k) i := by
      simpa using h_reflect
    -- Compute `2k + 1 - k = k + 1`.
    have h_start : 2 * k + 1 - k = k + 1 := by
      -- (2k + 1) - k = k + 1 on ℕ.
      have hk_le : k ≤ 2 * k + 1 := by
        have : k ≤ 2 * k := by
          have hk_ge1 : 1 ≤ k := hk
          calc
            k = 1 * k := by simp
            _ ≤ 2 * k := by
              have : 1 ≤ 2 := by decide
              exact Nat.mul_le_mul_right _ this
        exact le_trans this (Nat.le_succ _)
      have := Nat.add_sub_of_le hk_le
      -- `(k + (k + 1)) - k = k + 1`.
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using this
    -- Rewrite the right-hand index interval using `h_start`.
    have h_reflect'' :
        (∑ i ∈ Finset.Ico 0 k, Nat.choose (2 * k) (2 * k - i))
          = ∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), Nat.choose (2 * k) i := by
      simpa [h_start] using h_reflect'
    -- Combine symmetry and reflection.
    exact h_symm.trans h_reflect''
  -- Use the interval equalities to translate back to the original statement.
  calc
    ∑ i ∈ Finset.Icc 0 (k - 1), Nat.choose (2 * k) i
        = ∑ i ∈ Finset.Ico 0 k, Nat.choose (2 * k) i := by
          simpa [h_left]
    _ = ∑ i ∈ Finset.Ico (k + 1) (2 * k + 1), Nat.choose (2 * k) i := h_goal
    _ = ∑ i ∈ Finset.Icc (k + 1) (2 * k), Nat.choose (2 * k) i := by
          simpa [h_right]

open Finset in
theorem sum_ico_eq_sum_range (f : ℕ → ℝ) (n k : ℕ) (hkn : k ≤ n) : ∑ i ∈ Ico k (n + 1), f i = ∑ j ∈ range (n - k + 1), f (j + k) := by
  rw [Finset.sum_Ico_eq_sum_range]
  congr
  · omega
  · ext
    rw [add_comm]

open Finset in
noncomputable def L_aux (z : ℝ) : ℝ := Real.log (2 / Real.sqrt Real.pi) - z^2 + (3/2 : ℝ) * Real.log (z^2 + 1)

open Finset in
noncomputable def constant_C (k : ℕ) : ℝ :=
  let A := (1 / 2) * ((2 * k).choose k : ℝ) * k
  let B := Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi)
  Real.log (B / A)

open ProbabilityTheory ENNReal Set in
theorem pmf_tail_eq_one_sub_cdf (p : PMF ℕ) (k : ℕ) :
  ENNReal.toReal (p.toMeasure (Set.Ici k)) =
    1 - ENNReal.toReal (p.toMeasure {i | i < k}) := by
  haveI : MeasureTheory.IsProbabilityMeasure p.toMeasure := PMF.toMeasure.isProbabilityMeasure p
  have h_compl : Set.Ici k = {i | i < k}ᶜ := by
    ext x
    simp only [Set.mem_Ici, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rw [h_compl]
  have h_meas : MeasurableSet {i | i < k} := trivial
  rw [MeasureTheory.prob_compl_eq_one_sub h_meas]
  rw [ENNReal.toReal_sub_of_le MeasureTheory.prob_le_one ENNReal.one_ne_top]
  simp

open ProbabilityTheory ENNReal Set in
theorem pmf_map_coe_fin_apply_le (n : ℕ) (p : PMF (Fin (n + 1))) (k : ℕ) (h : k ≤ n) : p.map (fun i : Fin (n + 1) => (i : ℕ)) k = p ⟨k, Nat.lt_succ_of_le h⟩ := by
  rw [PMF.map_apply]
  let k_fin : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le h⟩
  trans ∑' (a : Fin (n + 1)), if a = k_fin then p a else 0
  · apply tsum_congr
    intro a
    congr 1
    simp only [k_fin, Fin.ext_iff]
    apply propext
    exact eq_comm
  · rw [tsum_ite_eq]

open ProbabilityTheory MeasureTheory in
theorem gaussian_cdf_eq_integral (y : ℝ) : cdf (gaussianReal 0 1) y = ∫ x in Set.Iic y, gaussianPDFReal 0 1 x := by
  rw [cdf_eq_real]
  rw [Measure.real]
  rw [gaussianReal_apply 0 one_ne_zero (Set.Iic y)]
  rw [integral_eq_lintegral_of_nonneg_ae]
  · congr
  · apply ae_of_all
    intro x
    apply gaussianPDFReal_nonneg
  · exact ((integrable_gaussianPDFReal 0 1).integrableOn).aestronglyMeasurable

open NNReal ENNReal ProbabilityTheory in
theorem binomial_pmf_map_support (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
  ((PMF.binomial p hp n).map (λ i => (i : ℕ))).support ⊆ {i | i ≤ n} := by
  intro i hi
  -- focus on the PMF appearing in the goal
  let q : PMF ℕ := Fin.val <$> PMF.binomial p hp n
  -- rewrite `hi` as membership in the support of `PMF.map id q`
  have hiq' : i ∈ (PMF.map (fun j : ℕ => j) q).support := by
    -- this is definitionally equal to the original PMF
    simpa [q, PMF.monad_map_eq_map] using hi
  -- from support of `PMF.map id q`, deduce support of `q`
  have hiq : i ∈ q.support := by
    rcases (PMF.mem_support_map_iff (f := fun j : ℕ => j) (p := q) (b := i)).1 hiq' with
      ⟨j, hj, hj_eq⟩
    have : j = i := by simpa using hj_eq
    simpa [this] using hj
  -- rewrite `hiq` so that `q` is expressed as a `map` of the binomial PMF
  have hiq_mem :
      i ∈ ((PMF.binomial p hp n).map (fun a : Fin (n + 1) => (↑a : ℕ))).support := by
    -- change the expression for `q` using `monad_map_eq_map`
    change
        i ∈ ((PMF.binomial p hp n).map (fun a : Fin (n + 1) => (↑a : ℕ))).support at hiq
    simpa [q, PMF.monad_map_eq_map] using hiq
  -- now use `mem_support_map_iff` for the map from `Fin (n+1)` to `ℕ`
  rcases
      (PMF.mem_support_map_iff
          (f := fun a : Fin (n + 1) => (↑a : ℕ))
          (p := PMF.binomial p hp n)
          (b := i)).1
        hiq_mem
      with
      ⟨a, ha_support, ha_eq⟩
  -- `ha_eq` tells us that `i` is the natural number corresponding to `a : Fin (n+1)`
  have hi_eq : i = (↑a : ℕ) := ha_eq.symm
  -- rewrite the goal using this equality
  subst hi_eq
  -- finally, use that an element of `Fin (n+1)` is strictly less than `n+1`
  exact Nat.lt_succ_iff.mp a.is_lt

open NNReal ENNReal ProbabilityTheory in
noncomputable def psi_def (k : ℕ) (p : ℝ) : ℝ :=
  let s := p * (1 - p)
  (k : ℝ) / (4 * s) - k + (k + 1 / 2 : ℝ) * Real.log s

open NNReal ENNReal ProbabilityTheory in
theorem div_sqrt_identity (z : ℝ) (hz : 0 < z) : z / Real.sqrt (z^2 + 1) = 1 / Real.sqrt (1 + (z⁻¹) ^ 2) := by
  have hz_ne : z ≠ 0 := ne_of_gt hz
  -- Factor the expression under the square root: z^2 + 1 = z^2 * (1 + (z⁻¹)^2)
  have h_factor : z ^ 2 + 1 = z ^ 2 * (1 + (z⁻¹) ^ 2) := by
    field_simp [hz_ne]
  -- Rewrite the denominator using this factorization
  have hz2_nonneg : (0 : ℝ) ≤ z ^ 2 := by
    have := sq_nonneg z
    simpa [pow_two] using this
  calc
    z / Real.sqrt (z ^ 2 + 1)
        = z / Real.sqrt (z ^ 2 * (1 + (z⁻¹) ^ 2)) := by
              simpa [h_factor]
    _ = z / (Real.sqrt (z ^ 2) * Real.sqrt (1 + (z⁻¹) ^ 2)) := by
              simpa [Real.sqrt_mul hz2_nonneg]  -- √(z^2 * a) = √(z^2) * √a
    _ = z / (z * Real.sqrt (1 + (z⁻¹) ^ 2)) := by
              have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
              have hsqrtz : Real.sqrt (z ^ 2) = z := by
                simpa using Real.sqrt_sq hz0
              simpa [hsqrtz, mul_comm]
    _ = 1 / Real.sqrt (1 + (z⁻¹) ^ 2) := by
              -- cancel the factor z in numerator and denominator
              have hden_ne : Real.sqrt (1 + (z⁻¹) ^ 2) ≠ 0 := by
                have h_pos : 0 < 1 + (z⁻¹) ^ 2 := by
                  have : 0 < (z⁻¹) ^ 2 + 1 :=
                    add_pos_of_nonneg_of_pos (sq_nonneg _) zero_lt_one
                  simpa [add_comm] using this
                exact Real.sqrt_ne_zero'.mpr h_pos
              field_simp [hz_ne, hden_ne]

open Filter Topology Set in
theorem unimodal_gap_lemma {f g : ℝ → ℝ} {a b : ℝ} (_ : a < b) (hcont : ContinuousOn (f - g) (Set.Icc a b)) (hdiff : DifferentiableOn ℝ (f - g) (Set.Ioo a b)) (ha : f a ≥ g a) (hb : f b ≥ g b) (h_sign : ∃ c ∈ Set.Ioo a b, (∀ x ∈ Set.Ioo a c, deriv (f - g) x ≥ 0) ∧ (∀ x ∈ Set.Ico c b, deriv (f - g) x ≤ 0)) : ∀ x ∈ Set.Icc a b, f x ≥ g x := by
  rcases h_sign with ⟨c, hc_in, h_pos, h_neg⟩
  let h := f - g
  have h_def : h = f - g := rfl
  have hac : a < c := hc_in.1
  have hcb : c < b := hc_in.2

  -- Monotonicity on [a, c]
  have h_mono : MonotoneOn h (Icc a c) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a c)
    · apply hcont.mono
      exact Icc_subset_Icc_right (le_of_lt hcb)
    · apply hdiff.mono
      rw [interior_Icc]
      exact Ioo_subset_Ioo (le_refl a) (le_of_lt hcb)
    · intro x hx
      rw [interior_Icc] at hx
      exact h_pos x hx

  -- Monotonicity on [c, b]
  have h_anti : AntitoneOn h (Icc c b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc c b)
    · apply hcont.mono
      exact Icc_subset_Icc_left (le_of_lt hac)
    · apply hdiff.mono
      rw [interior_Icc]
      exact Ioo_subset_Ioo (le_of_lt hac) (le_refl b)
    · intro x hx
      rw [interior_Icc] at hx
      apply h_neg
      exact Ioo_subset_Ico_self hx

  intro x hx
  simp only [ge_iff_le]
  -- We want to prove g x ≤ f x, i.e., 0 ≤ f x - g x
  rw [← sub_nonneg]
  change 0 ≤ h x

  by_cases hxc : x ≤ c
  · -- Case x in [a, c]
    have hx_in : x ∈ Icc a c := ⟨hx.1, hxc⟩
    have ha_in : a ∈ Icc a c := ⟨le_refl a, le_of_lt hac⟩
    have : h a ≤ h x := h_mono ha_in hx_in hx.1
    have : 0 ≤ h a := by
      rw [h_def]
      simp only [Pi.sub_apply]
      rw [sub_nonneg]
      exact ha
    linarith
  · -- Case x in [c, b]
    push_neg at hxc
    have hx_in : x ∈ Icc c b := ⟨le_of_lt hxc, hx.2⟩
    have hb_in : b ∈ Icc c b := ⟨le_of_lt hcb, le_refl b⟩
    have : h x ≥ h b := h_anti hx_in hb_in hx.2
    have : 0 ≤ h b := by
      rw [h_def]
      simp only [Pi.sub_apply]
      rw [sub_nonneg]
      exact hb
    linarith

open Filter Topology Set in
theorem tendsto_sqrt_inv_mul (a : ℝ) (ha : 0 < a) : Filter.Tendsto (fun p : ℝ => Real.sqrt (a / p)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have h1 : Tendsto (fun x : ℝ => x⁻¹) (nhdsWithin 0 (Ioi 0)) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun x : ℝ => a * x⁻¹) (nhdsWithin 0 (Ioi 0)) atTop := Filter.Tendsto.const_mul_atTop ha h1
  have h3 : Tendsto (fun x : ℝ => x ^ (1/2 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  apply (h3.comp h2).congr'
  filter_upwards with x
  simp [Real.sqrt_eq_rpow, div_eq_mul_inv]

open Filter Topology in
theorem unimodal_nonneg_of_deriv (f : ℝ → ℝ) (f' : ℝ → ℝ) (hf : ∀ x, 0 ≤ x → HasDerivAt f (f' x) x) (h0 : f 0 = 0) (h_lim : Filter.Tendsto f Filter.atTop (nhds 0)) (h_shape : ∃ x0 > 0, (∀ x, 0 ≤ x → x ≤ x0 → f' x ≥ 0) ∧ (∀ x, x ≥ x0 → f' x ≤ 0)) : ∀ x, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  rcases h_shape with ⟨x0, hx0_pos, h_incr, h_decr⟩
  by_cases h : x ≤ x0
  · -- Case 1: x in [0, x0]
    have h_mono : MonotoneOn f (Set.Icc 0 x0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x0)
      · intro y hy
        exact (hf y hy.1).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact (hf y (le_of_lt hy.1)).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact h_incr y (le_of_lt hy.1) (le_of_lt hy.2)
    have h_0_mem : 0 ∈ Set.Icc 0 x0 := ⟨le_rfl, le_of_lt hx0_pos⟩
    have h_x_mem : x ∈ Set.Icc 0 x0 := ⟨hx, h⟩
    have h_ineq := h_mono h_0_mem h_x_mem hx
    rwa [h0] at h_ineq
  · -- Case 2: x > x0
    push_neg at h
    have h_anti : AntitoneOn f (Set.Ici x0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici x0)
      · intro y hy
        exact (hf y (le_trans (le_of_lt hx0_pos) hy)).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        exact (hf y (le_trans (le_of_lt hx0_pos) (le_of_lt hy))).hasDerivWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        exact h_decr y (le_of_lt hy)
    have h_ev : ∀ᶠ y in atTop, f y ≤ f x := by
      rw [eventually_atTop]
      use x
      intro y hy
      apply h_anti (le_of_lt h) (le_trans (le_of_lt h) hy) hy
    apply le_of_tendsto h_lim h_ev

open Filter Topology in
theorem hasDerivAt_y_mul_one_sub_y (p : ℝ) : HasDerivAt (fun y : ℝ => y * (1 - y)) (1 - 2 * p) p := by
  -- Rewrite y * (1 - y) as y - y^2 and use power rule
  have h_eq : (fun y : ℝ => y * (1 - y)) = fun y : ℝ => y - y^2 := by
    funext y
    ring
  -- Derivative of y is 1
  have h_id : HasDerivAt (fun y : ℝ => y) 1 p := by
    simpa using (hasDerivAt_id (x := p))
  -- Derivative of y^2 is 2 * y, so at p it is 2 * p
  have h_sq : HasDerivAt (fun y : ℝ => y ^ (2 : ℕ)) (2 * p) p := by
    -- use lemma hasDerivAt_pow for the identity function
    have h : HasDerivAt (fun y : ℝ => y) 1 p := h_id
    -- apply power rule for functions
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using (HasDerivAt.fun_pow h 2)
  -- Therefore derivative of - y^2 is - (2*p)
  have h_neg_sq : HasDerivAt (fun y : ℝ => - y^2) (- (2 * p)) p := by
    -- rewrite -y^2 as (-1) * y^2 and use multiplication by constant
    -- First get derivative of y^2 as above but stated slightly differently
    have h_sq' : HasDerivAt (fun y : ℝ => y^2) (2 * p) p := by
      simpa [pow_two] using h_sq
    simpa [neg_mul, pow_two] using h_sq'.neg
  -- Combine: derivative of y - y^2 is 1 - 2*p
  have h_main : HasDerivAt (fun y : ℝ => y - y^2) (1 - 2 * p) p := by
    -- rewrite as y + (-y^2)
    have h_neg_sq' : HasDerivAt (fun y : ℝ => - y^2) (- (2 * p)) p := h_neg_sq
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_mul, pow_two] using
      h_id.add h_neg_sq'
  -- Transfer derivative back along equality of functions
  simpa [h_eq] using h_main

open Filter Topology in
noncomputable def binomial_term (n i : ℕ) (x : ℝ) : ℝ := (n.choose i) * x ^ i * (1 - x) ^ (n - i)

open NNReal ENNReal ProbabilityTheory in
noncomputable def binomial_gaussian_gap (p : ℝ) (hp : p ∈ Set.Ioo 0 (1 / 2)) (k : ℕ) (σ : ℝ) : ℝ :=
  let p_nn : ℝ≥0 := ⟨p, le_of_lt hp.1⟩
  have h_lt : (p_nn : ℝ) < 1 := lt_trans hp.2 (by norm_num)
  let hp_le : p_nn ≤ 1 := le_of_lt h_lt
  let tail := ENNReal.toReal (((PMF.binomial p_nn hp_le (2 * k)).map (λ i => (i : ℕ))).toMeasure (Set.Ici k))
  let gauss := 1 - cdf (gaussianReal 0 1) ((1 / 2 - p) * Real.sqrt (2 * k) / σ)
  tail - gauss

open Finset in
noncomputable def midpoint_tail_S (n k : ℕ) (p : ℝ) : ℝ :=
  (1 / 2) * ((∑ i ∈ Finset.Ico k (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)) +
             (∑ i ∈ Finset.Ico (k + 1) (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)))

open Finset in
theorem function_A_sq_identity_helper (p : ℝ) : (1 / 2 - p) ^ 2 = p ^ 2 - p + (1 / 4 : ℝ) := by
  ring_nf

open Finset in
noncomputable def midpoint_tail_polynomial_v2 (n k : ℕ) (p : ℝ) : ℝ :=
  (1 / 2) * ((∑ i ∈ Finset.Ico k (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)) +
             (∑ i ∈ Finset.Ico (k + 1) (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)))

open Finset in
noncomputable def R_aux (z : ℝ) : ℝ := 2 / Real.sqrt Real.pi * Real.exp (-z^2) * (z^2 + 1) ^ (3/2 : ℝ)

open ENNReal NNReal in
theorem binomial_tail_prob_le_one (p : ℝ≥0) (hp : p ≤ (1 : ℝ≥0)) (n k : ℕ) (hk : k < n + 1) : ((PMF.binomial p hp n).toMeasure (Set.Ici ⟨k, hk⟩)).toReal ≤ 1 := by
  let μ := (PMF.binomial p hp n).toMeasure
  have : MeasureTheory.IsProbabilityMeasure μ := PMF.toMeasure.isProbabilityMeasure _
  have h : μ (Set.Ici ⟨k, hk⟩) ≤ 1 := MeasureTheory.prob_le_one
  rw [← ENNReal.toReal_one, ENNReal.toReal_le_toReal]
  · exact h
  · exact MeasureTheory.measure_ne_top _ _
  · exact ENNReal.one_ne_top

open Filter Topology Set in
theorem tendsto_atTop_of_eventually_ge {α : Type*} (l : Filter α) (f g : α → ℝ) (hg : Filter.Tendsto g l Filter.atTop) (hge : ∀ᶠ x in l, g x ≤ f x) : Filter.Tendsto f l Filter.atTop := by
  -- We can use the general monotonicity lemma `Filter.tendsto_atTop_mono'`
  -- which states: if f₁ ≤ᶠ[l] f₂ and f₁ → atTop then f₂ → atTop.
  -- Here we take f₁ = g and f₂ = f.
  exact Filter.tendsto_atTop_mono' l hge hg

open Filter Topology Set in
theorem gaussian_tail_bound_region2_identity (p : ℝ) : 1 - (1 / 2 - p) / Real.sqrt ((1 / 2 - p) ^ 2 + p * (1 - p)) = 2 * p := by
  have h1 : (1 / 2 - p) ^ 2 + p * (1 - p) = (1 / 4 : ℝ) := by
    ring
  have hsqrt1 : Real.sqrt ((1 / 2 - p) ^ 2 + p * (1 - p)) = Real.sqrt (1 / 4 : ℝ) := by
    simpa using congrArg (fun x : ℝ => Real.sqrt x) h1
  have hsqrtquarter : Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
    -- evaluate the square root numerically
    -- norm_num knows that √(1/4) = 1/2 (up to normalization)
    norm_num
  have hsqrt : Real.sqrt ((1 / 2 - p) ^ 2 + p * (1 - p)) = (1 / 2 : ℝ) :=
    Eq.trans hsqrt1 hsqrtquarter
  have hstep1 : 1 - (1 / 2 - p) / Real.sqrt ((1 / 2 - p) ^ 2 + p * (1 - p))
      = 1 - (1 / 2 - p) / (1 / 2 : ℝ) := by
    have := congrArg (fun x : ℝ => 1 - (1 / 2 - p) / x) hsqrt
    simpa using this
  calc
    1 - (1 / 2 - p) / Real.sqrt ((1 / 2 - p) ^ 2 + p * (1 - p))
        = 1 - (1 / 2 - p) / (1 / 2 : ℝ) := hstep1
    _ = 2 * p := by
      -- simplify this purely algebraic identity
      have : 1 - (1 / 2 - p) / (1 / 2 : ℝ) = 2 * p := by
        -- rewrite the division as multiplication by the inverse and simplify
        field_simp
        ring
      simpa using this

open Finset in
theorem sum_choose_split_at_middle_real (k : ℕ) (hk : 0 < k) :
  let n := 2 * k;
  ∑ i ∈ Finset.Icc 0 n, (Nat.choose n i : ℝ)
    = (∑ i ∈ Finset.Icc 0 (k - 1), (Nat.choose n i : ℝ))
      + (Nat.choose n k : ℝ)
      + (∑ i ∈ Finset.Icc (k + 1) n, (Nat.choose n i : ℝ)) := by
  classical
  -- Simplify the `let`-binding so everything is expressed in terms of `2 * k`.
  simp
  -- Goal now:
  -- ⊢ ∑ i ∈ Icc 0 (2 * k), ↑((2 * k).choose i)
  --     = ∑ i ∈ Icc 0 (k - 1), ↑((2 * k).choose i)
  --       + ↑((2 * k).choose k)
  --       + ∑ i ∈ Icc (k + 1) (2 * k), ↑((2 * k).choose i)

  -- 1. Decompose the index interval `[0, 2*k]` as `[0, k] ∪ [k+1, 2*k]`.
  have hdecomp :
      (Icc 0 (2 * k) : Finset ℕ) = Icc 0 k ∪ Icc (k + 1) (2 * k) := by
    ext i; constructor
    · intro hi
      rcases mem_Icc.mp hi with ⟨hi0, hi2k⟩
      -- Either `i ≤ k` or `k + 1 ≤ i`.
      have hcases : i ≤ k ∨ k + 1 ≤ i := by
        have hk_total := le_total i k
        rcases hk_total with hle | hge
        · exact Or.inl hle
        · rcases Nat.eq_or_lt_of_le hge with h_eq | h_lt
          · -- `i = k`
            left; exact h_eq.ge
          · -- `k < i`, hence `k + 1 ≤ i`.
            right; exact Nat.succ_le_of_lt h_lt
      rcases hcases with hle | hge
      · -- `i ∈ [0, k]`
        have hiIcc : i ∈ Icc 0 k := mem_Icc.mpr ⟨hi0, hle⟩
        have : i ∈ Icc 0 k ∨ i ∈ Icc (k + 1) (2 * k) := Or.inl hiIcc
        simpa [Finset.mem_union] using this
      · -- `i ∈ [k+1, 2*k]`
        have hiIcc : i ∈ Icc (k + 1) (2 * k) := mem_Icc.mpr ⟨hge, hi2k⟩
        have : i ∈ Icc 0 k ∨ i ∈ Icc (k + 1) (2 * k) := Or.inr hiIcc
        simpa [Finset.mem_union] using this
    · intro hi
      -- `i` lies in one of the two pieces, so it lies in `[0, 2*k]`.
      have : i ∈ Icc 0 k ∨ i ∈ Icc (k + 1) (2 * k) := by
        simpa [Finset.mem_union] using hi
      rcases this with hi0k | hik2k
      · -- case `i ∈ [0, k]`
        rcases mem_Icc.mp hi0k with ⟨hi0, hik⟩
        have hk_le_2k : k ≤ 2 * k := by
          have h12 : (1 : ℕ) ≤ 2 := by decide
          simpa [one_mul] using Nat.mul_le_mul_right k h12
        have hi2k : i ≤ 2 * k := le_trans hik hk_le_2k
        exact mem_Icc.mpr ⟨hi0, hi2k⟩
      · -- case `i ∈ [k+1, 2*k]`
        rcases mem_Icc.mp hik2k with ⟨hik1, hi2k⟩
        have hi0 : 0 ≤ i := Nat.zero_le _
        exact mem_Icc.mpr ⟨hi0, hi2k⟩

  have hdisj : Disjoint (Icc 0 k : Finset ℕ) (Icc (k + 1) (2 * k) : Finset ℕ) := by
    refine Finset.disjoint_left.mpr ?_
    intro i hi0k hik2k
    rcases mem_Icc.mp hi0k with ⟨_, hik⟩
    rcases mem_Icc.mp hik2k with ⟨hik1, _⟩
    -- We get `i ≤ k` and `k + 1 ≤ i`, impossible.
    have hk1_le_k : k + 1 ≤ k := le_trans hik1 hik
    exact Nat.not_succ_le_self k hk1_le_k

  -- Use the decomposition and disjointness to split the sum.
  have hsplit1 :
      (∑ i ∈ Icc 0 (2 * k), ((2 * k).choose i : ℝ))
        = (∑ i ∈ Icc 0 k, ((2 * k).choose i : ℝ))
          + (∑ i ∈ Icc (k + 1) (2 * k), ((2 * k).choose i : ℝ)) := by
    have :=
      (Finset.sum_union (s₁ := (Icc 0 k : Finset ℕ))
        (s₂ := Icc (k + 1) (2 * k))
        (f := fun i => ((2 * k).choose i : ℝ)) hdisj)
    -- `sum_union` gives the equality over the union; rewrite the union as `Icc 0 (2*k)`.
    simpa [hdecomp.symm] using this

  -- 2. Split the sum over `[0, k]` to separate out the term at `k`.
  have hsplit2 :
      (∑ i ∈ Icc 0 k, ((2 * k).choose i : ℝ))
        = (∑ i ∈ Icc 0 (k - 1), ((2 * k).choose i : ℝ))
          + ((2 * k).choose k : ℝ) := by
    -- This is the additive version of `Finset.prod_Icc_succ_top` with `a = 0`, `b = k - 1`.
    have hle : 0 ≤ (k - 1) + 1 := Nat.zero_le _
    have hk1 : 1 ≤ k := Nat.succ_le_of_lt hk
    -- `sum_Icc_succ_top` states:
    --   ∑_{i ∈ Icc 0 ((k-1)+1)} f i = ∑_{i ∈ Icc 0 (k-1)} f i + f ((k-1)+1).
    -- We rewrite `((k-1)+1)` to `k` using `Nat.sub_add_cancel hk1`.
    simpa [Nat.sub_add_cancel hk1, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_Icc_succ_top (a := 0) (b := k - 1)
        (hab := hle) (f := fun i => ((2 * k).choose i : ℝ)))

  -- 3. Combine the two splittings and reassociate additions.
  calc
    ∑ i ∈ Icc 0 (2 * k), ((2 * k).choose i : ℝ)
        = (∑ i ∈ Icc 0 k, ((2 * k).choose i : ℝ))
          + (∑ i ∈ Icc (k + 1) (2 * k), ((2 * k).choose i : ℝ)) := hsplit1
    _ = ((∑ i ∈ Icc 0 (k - 1), ((2 * k).choose i : ℝ))
          + ((2 * k).choose k : ℝ))
          + (∑ i ∈ Icc (k + 1) (2 * k), ((2 * k).choose i : ℝ)) := by
            simpa [hsplit2, add_assoc]
    _ = (∑ i ∈ Icc 0 (k - 1), ((2 * k).choose i : ℝ))
          + ((2 * k).choose k : ℝ)
          + (∑ i ∈ Icc (k + 1) (2 * k), ((2 * k).choose i : ℝ)) := by
            simp [add_left_comm, add_assoc]
    _ = _ := rfl

open Finset in
theorem sigma_pos (p : ℝ) (hp : p ∈ Set.Ioo 0 (1 / 2)) : 0 < (p * (1 - p)).sqrt := by
  apply Real.sqrt_pos.mpr
  have h1 : 0 < p := hp.1
  have h2 : p < 1 / 2 := hp.2
  have h3 : 0 < 1 - p := by linarith
  exact _root_.mul_pos h1 h3

open Set in
theorem mul_one_sub_strictMono_Ioo_zero_half: StrictMonoOn (fun p : ℝ => p * (1 - p)) (Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) := by
  intro a ha b hb hlt
  have hba : 0 < b - a := sub_pos.mpr hlt
  have ha_half : a < (1 : ℝ) / 2 := ha.2
  have hb_half : b < (1 : ℝ) / 2 := hb.2
  have hab_lt_one : a + b < 1 := by
    have h1 : a + b < (1 : ℝ) / 2 + (1 : ℝ) / 2 := add_lt_add ha_half hb_half
    -- Rewrite the right-hand side to 1
    have hhalf : (1 : ℝ) / 2 = (2 : ℝ)⁻¹ := by norm_num
    have hsum : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
    -- Now convert the goal using these equalities
    have : a + b < (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ := by simpa [hhalf] using h1
    simpa [hsum] using this
  have hab_pos : 0 < 1 - (a + b) := sub_pos.mpr hab_lt_one
  have hdiff : (fun p : ℝ => p * (1 - p)) b - (fun p : ℝ => p * (1 - p)) a
      = (b - a) * (1 - (a + b)) := by
    -- Use ring to expand and simplify
    have : b * (1 - b) - a * (1 - a) = (b - a) * (1 - (a + b)) := by
      ring
    simpa using this
  have hpos : 0 < (fun p : ℝ => p * (1 - p)) b
      - (fun p : ℝ => p * (1 - p)) a := by
    have : 0 < (b - a) * (1 - (a + b)) := mul_pos hba hab_pos
    simpa [hdiff] using this
  have : (fun p : ℝ => p * (1 - p)) a < (fun p : ℝ => p * (1 - p)) b := sub_pos.mp hpos
  simpa using this

open NNReal ENNReal ProbabilityTheory in
lemma sub_ge_iff_le_add (a b c : ℝ) : a - b ≥ c ↔ b + c ≤ a := by
  constructor
  · intro h
    -- Interpret `≥` as `≤` with flipped arguments.
    have h' : c ≤ a - b := h
    -- Use the standard lemma `le_sub_iff_add_le`.
    have h'' : c + b ≤ a := (le_sub_iff_add_le.mp h')
    -- Reorder the sum on the left.
    simpa [add_comm] using h''
  · intro h
    -- From `b + c ≤ a`, get `c + b ≤ a`.
    have h' : c + b ≤ a := by
      simpa [add_comm] using h
    -- Now apply the lemma in the other direction.
    have h'' : c ≤ a - b := (le_sub_iff_add_le.mpr h')
    -- Interpret this back as `a - b ≥ c`.
    exact h''

open NNReal ENNReal ProbabilityTheory in
theorem conjecture6_3_reformulated (p : ℝ) (h_p : p ∈ Set.Ioo 0 (1 / 2)) (k : ℕ) (_ : 0 < k) (σ : ℝ) (_ : σ = (p * (1 - p)).sqrt) :
  let hp' := p_to_nnreal_le_one p h_p;
  let G : ℝ :=
    ((PMF.binomial (⟨p, le_of_lt h_p.1⟩) hp' (2 * k)).toMeasure
      (Set.Ici ⟨k, Nat.lt_add_one_iff.mpr (Nat.le_mul_of_pos_left k (by omega : 0 < 2))⟩)).toReal
    - (1 - cdf (gaussianReal 0 1) ((1 / 2 - p) * Real.sqrt (2 * k) / σ));
  G ≥ (1 / 2) * ((2 * k).choose k) * σ ^ (2 * k)
  ↔
  1 - cdf (gaussianReal 0 1) ((1 / 2 - p) * Real.sqrt (2 * k) / σ)
    + (1 / 2) * ((2 * k).choose k) * σ ^ (2 * k)
    ≤ ((PMF.binomial (⟨p, le_of_lt h_p.1⟩) hp' (2 * k)).toMeasure
        (Set.Ici ⟨k, Nat.lt_add_one_iff.mpr (Nat.le_mul_of_pos_left k (by omega : 0 < 2))⟩)).toReal := by
  classical
  -- Rewrite the statement to inline the `let`-bindings `hp'` and `G`.
  change
    ((((PMF.binomial (⟨p, le_of_lt h_p.1⟩)
            (p_to_nnreal_le_one p h_p) (2 * k)).toMeasure
            (Set.Ici
              ⟨k,
                Nat.lt_add_one_iff.mpr
                  (Nat.le_mul_of_pos_left k (by omega : 0 < 2))⟩)).toReal
        -
        (1 -
          cdf (gaussianReal 0 1)
            ((1 / 2 - p) * Real.sqrt (2 * k) / σ)))
        ≥
        (1 / 2) * ((2 * k).choose k) * σ ^ (2 * k))
      ↔
      1 -
          cdf (gaussianReal 0 1)
            ((1 / 2 - p) * Real.sqrt (2 * k) / σ) +
        (1 / 2) * ((2 * k).choose k) * σ ^ (2 * k)
        ≤
        (((PMF.binomial (⟨p, le_of_lt h_p.1⟩)
              (p_to_nnreal_le_one p h_p) (2 * k)).toMeasure
              (Set.Ici
                ⟨k,
                  Nat.lt_add_one_iff.mpr
                    (Nat.le_mul_of_pos_left k (by omega : 0 < 2))⟩)).toReal)
  -- Now this is a purely algebraic fact over `ℝ`.
  -- Apply the generic lemma `sub_ge_iff_le_add`.
  simpa using
    (sub_ge_iff_le_add
      ((((PMF.binomial (⟨p, le_of_lt h_p.1⟩)
              (p_to_nnreal_le_one p h_p) (2 * k)).toMeasure
              (Set.Ici
                ⟨k,
                  Nat.lt_add_one_iff.mpr
                    (Nat.le_mul_of_pos_left k (by omega : 0 < 2))⟩)).toReal))
      (1 -
        cdf (gaussianReal 0 1)
          ((1 / 2 - p) * Real.sqrt (2 * k) / σ))
      ((1 / 2) * ((2 * k).choose k) * σ ^ (2 * k)))

open NNReal ENNReal ProbabilityTheory in
noncomputable def binomial_tail_prob (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (n k : ℕ) : ℝ :=
  let p_nn : NNReal := ⟨p, le_of_lt hp.1⟩
  let hp_le : p_nn ≤ 1 := le_of_lt hp.2
  ENNReal.toReal (((PMF.binomial p_nn hp_le n).map (λ i => (i : ℕ))).toMeasure (Set.Ici k))

open NNReal ENNReal ProbabilityTheory in
theorem gaussian_core_fun_deriv (u : ℝ) (hu : 0 < u) : HasDerivAt gaussian_core_fun (2 * u^(1/2 : ℝ) * Real.exp (1 - u) * ((3/2 : ℝ) - u)) u := by
  -- derivative of x ↦ x^(3/2)
  have h_pow : HasDerivAt (fun x : ℝ => x^(3/2 : ℝ)) ((3/2 : ℝ) * u^((3/2 : ℝ) - 1)) u := by
    have h := (HasDerivAt.rpow_const (f := fun x : ℝ => x) (f' := (1 : ℝ)) (x := u)
      (hf := hasDerivAt_id u) (hx := Or.inr (by norm_num : (1 : ℝ) ≤ (3/2 : ℝ))))
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc, one_mul, id] using h
  -- simplify exponent to 1/2
  have h_pow' : HasDerivAt (fun x : ℝ => x^(3/2 : ℝ)) ((3/2 : ℝ) * u^(1/2 : ℝ)) u := by
    have h_exp : (3/2 : ℝ) - 1 = (1/2 : ℝ) := by norm_num
    simpa [h_exp] using h_pow
  -- derivative of x ↦ 1 - x
  have h_inner : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
    have h := (HasDerivAt.const_sub (c := (1 : ℝ)) (hf := hasDerivAt_id u))
    simpa [sub_eq_add_neg, one_mul, id] using h
  -- compose with exp
  have h_exp : HasDerivAt (fun x : ℝ => Real.exp (1 - x)) (Real.exp (1 - u) * (-1)) u := by
    simpa using h_inner.exp
  -- product rule with constant multiple 2
  have h := (h_pow'.const_mul (2 : ℝ)).mul h_exp
  -- transfer derivative to gaussian_core_fun using congr_of_eventuallyEq
  have h_fun : gaussian_core_fun
      = ((fun x : ℝ => 2 * x^(3/2 : ℝ)) * fun x : ℝ => Real.exp (1 - x)) := by
    funext x
    simp [gaussian_core_fun, mul_comm, mul_left_comm, mul_assoc]
  have h_eq : gaussian_core_fun
      =ᶠ[nhds u] ((fun x : ℝ => 2 * x^(3/2 : ℝ)) * fun x : ℝ => Real.exp (1 - x)) :=
    Filter.EventuallyEq.of_eq h_fun
  have h_gauss := h.congr_of_eventuallyEq h_eq
  -- simplify function and derivative expression
  have h_core' :
      HasDerivAt gaussian_core_fun
        (2 * (u ^ (1/2 : ℝ) * ((3/2 : ℝ) * Real.exp (1 - u)))
          + -(2 * (u ^ (3/2 : ℝ) * Real.exp (1 - u)))) u := by
    simpa [gaussian_core_fun, mul_comm, mul_left_comm, mul_assoc,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_gauss
  -- algebraic simplification of the derivative
  have h_simpl :
      2 * (u ^ (1/2 : ℝ) * ((3/2 : ℝ) * Real.exp (1 - u)))
        + -(2 * (u ^ (3/2 : ℝ) * Real.exp (1 - u)))
      = 2 * u^(1/2 : ℝ) * Real.exp (1 - u) * ((3/2 : ℝ) - u) := by
    have hu_pos : 0 < u := hu
    -- rewrite u^(3/2) as u^(1/2) * u
    have hpow_id : u^(3/2 : ℝ) = u^(1/2 : ℝ) * u := by
      have h_add : u^((1/2 : ℝ) + 1) = u^(1/2 : ℝ) * u^1 := by
        simpa using (Real.rpow_add hu_pos (1/2 : ℝ) (1 : ℝ))
      have h_exp : (3/2 : ℝ) = (1/2 : ℝ) + 1 := by norm_num
      simpa [h_exp, Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using h_add
    -- step 1: rewrite the second term using hpow_id
    have hA :
        2 * (u ^ (1/2 : ℝ) * ((3/2 : ℝ) * Real.exp (1 - u)))
          + -(2 * (u ^ (3/2 : ℝ) * Real.exp (1 - u)))
        = 2 * (u ^ (1/2 : ℝ) * ((3/2 : ℝ) * Real.exp (1 - u)))
          + -(2 * ((u ^ (1/2 : ℝ) * u) * Real.exp (1 - u))) := by
      simp [hpow_id, mul_comm, mul_left_comm, mul_assoc]
    -- step 2: factor out 2 * u^(1/2) * exp(1 - u)
    have hB :
        2 * (u ^ (1/2 : ℝ) * ((3/2 : ℝ) * Real.exp (1 - u)))
          + -(2 * ((u ^ (1/2 : ℝ) * u) * Real.exp (1 - u)))
        = 2 * u^(1/2 : ℝ) * Real.exp (1 - u) * ((3/2 : ℝ) - u) := by
      ring_nf
    exact hA.trans hB
  -- adjust the derivative using h_simpl
  have h_core :
      HasDerivAt gaussian_core_fun
        (2 * u^(1/2 : ℝ) * Real.exp (1 - u) * ((3/2 : ℝ) - u)) u :=
    h_core'.congr_deriv h_simpl
  exact h_core

open ProbabilityTheory Set in
theorem gaussian_cdf_deriv (x : ℝ) : deriv (fun y => cdf (gaussianReal 0 1) y) x = gaussianPDFReal 0 1 x := by
  let f := gaussianPDFReal 0 1
  -- 1. Continuity of the PDF
  have h_cont : Continuous f := by
    simp only [f]
    rw [gaussianPDFReal_def]
    continuity

  -- 2. Express cdf as integral of PDF
  have h_cdf : ∀ y, cdf (gaussianReal 0 1) y = ∫ t in Iic y, f t := by
    intro y
    rw [cdf_eq_real]
    rw [MeasureTheory.measureReal_def]
    have h_meas_eq : gaussianReal 0 1 (Iic y) = ENNReal.ofReal (∫ t in Iic y, f t) := by
       rw [gaussianReal_apply_eq_integral (μ := 0) (v := 1) (by norm_num) (Iic y)]
    rw [h_meas_eq]
    rw [ENNReal.toReal_ofReal]
    · apply MeasureTheory.setIntegral_nonneg measurableSet_Iic
      intro t _
      apply gaussianPDFReal_nonneg

  -- 3. Derivative calculation using Fundamental Theorem of Calculus
  apply HasDerivAt.deriv
  let a := x - 1
  have ha : a < x := by linarith

  -- Split the integral into a constant part (-∞, a] and a variable part (a, y]
  apply HasDerivAt.congr_of_eventuallyEq (f := fun y => (∫ t in Iic a, f t) + ∫ t in a..y, f t)

  -- The derivative of the split form is f(x)
  · apply HasDerivAt.const_add
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (integrable_gaussianPDFReal 0 1).intervalIntegrable
    · exact h_cont.stronglyMeasurableAtFilter _ _
    · exact h_cont.continuousAt

  -- Show the split form is equal to the CDF near x
  · filter_upwards [Ioi_mem_nhds ha] with y hy
    rw [h_cdf y]
    have h_split : ∫ t in a..y, f t = (∫ t in Iic y, f t) - ∫ t in Iic a, f t := by
       rw [intervalIntegral.integral_Iic_sub_Iic]
       · exact (integrable_gaussianPDFReal 0 1).integrableOn
       · exact (integrable_gaussianPDFReal 0 1).integrableOn
    rw [h_split]
    abel

open ProbabilityTheory Set in
theorem gaussian_pdf_bound (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 / Real.sqrt (2 * Real.pi) := by
  rw [gaussianPDFReal_std, one_div]
  apply mul_le_of_le_one_right
  · apply inv_nonneg.mpr
    apply Real.sqrt_nonneg
  · rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · rw [neg_nonpos]
      apply sq_nonneg
    · norm_num

open ProbabilityTheory Set in
theorem continuous_telescoping_term (n k : ℕ) : Continuous (fun x : ℝ => telescoping_term n k x) := by
  unfold telescoping_term
  -- try to build continuity step by step
  have h1 : Continuous fun x : ℝ => (n : ℝ) * ((n - 1).choose k : ℝ) := by
    exact continuous_const
  have h2 : Continuous fun x : ℝ => x ^ k := by
    simpa using (continuous_id.pow k)
  have h3 : Continuous fun x : ℝ => (1 - x) ^ (n - 1 - k) := by
    have h_sub : Continuous fun x : ℝ => (1 : ℝ) - x := by
      exact continuous_const.sub continuous_id
    simpa using h_sub.pow (n - 1 - k)
  have h12 : Continuous fun x : ℝ => (n : ℝ) * ((n - 1).choose k : ℝ) * x ^ k := by
    exact (h1.mul h2)
  have h_all : Continuous fun x : ℝ => (n : ℝ) * ((n - 1).choose k : ℝ) * x ^ k * (1 - x) ^ (n - 1 - k) := by
    exact (h12.mul h3)
  simpa [mul_comm, mul_left_comm, mul_assoc] using h_all

open Filter Topology in
theorem limit_aux_power_exp (k c : ℝ) (hc : 0 < c) : Filter.Tendsto (fun p : ℝ => p^(-k) * Real.exp (-c/p)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  classical
  -- Define the Gaussian-type function on ℝ
  let g : ℝ → ℝ := fun x => x ^ k * Real.exp (-c * x)
  have hg : Tendsto g atTop (nhds 0) := gaussian_limit_zero_helper k c hc
  -- The inversion map tends to +∞ as p → 0⁺
  have hinv : Tendsto (fun p : ℝ => p⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) atTop := by
    simpa using (tendsto_inv_nhdsGT_zero :
      Tendsto (fun p : ℝ => p⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) atTop)
  -- Compose the two limits
  have hcomp : Tendsto (fun p : ℝ => g (p⁻¹)) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) :=
    hg.comp hinv
  -- Show the given function is eventually equal to the composed one on (0, ∞)
  refine (hcomp.congr' ?hEq)
  -- pointwise simplification for p > 0
  refine (Filter.eventually_iff_exists_mem.2 ?_)
  refine ⟨Set.Ioi (0 : ℝ), ?_, ?_⟩
  · exact self_mem_nhdsWithin
  · intro p hp
    have hp_pos : 0 < p := hp
    have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
    -- unfold definitions and use real power identities
    dsimp [g]
    -- (p⁻¹) ^ k = p ^ (-k)
    have hpow : (p⁻¹) ^ k = p ^ (-k) := by
      -- from nonneg, we have: p ^ (-k) = (p ^ k)⁻¹ and (p⁻¹) ^ k = (p ^ k)⁻¹
      have h1 : p ^ (-k) = (p ^ k)⁻¹ := by
        simpa using (Real.rpow_neg hp_nonneg k)
      have h2 : (p⁻¹) ^ k = (p ^ k)⁻¹ := by
        simpa using (Real.inv_rpow hp_nonneg k)
      -- combine
      calc
        (p⁻¹) ^ k = (p ^ k)⁻¹ := h2
        _ = p ^ (-k) := h1.symm
    -- simplify the exponential part: -c * p⁻¹ = -c / p
    have hexp : -c * p⁻¹ = -c / p := by
      field_simp [div_eq_mul_inv]
    -- Now show the desired equality
    -- Left side is g (p⁻¹), right side is the target expression
    have : g (p⁻¹) = p ^ (-k) * Real.exp (-c / p) := by
      -- start from the definition of g
      have : g (p⁻¹) = (p⁻¹) ^ k * Real.exp (-c * p⁻¹) := rfl
      -- rewrite powers and exponential argument
      simpa [this, hpow, hexp]
    -- rewrite left-hand side using the above identity
    simpa [g, hexp, hpow] using this.symm

open Filter Topology in
theorem gaussian_limit_zero_helper_sq (k c : ℝ) (hc : 0 < c) : Tendsto (fun x => x ^ k * Real.exp (-c * x ^ 2)) atTop (nhds 0) := by
  -- We use the helper with exponent k/2 and substitution u = x^2.
  -- Step 1: instantiate the helper with exponent k/2.
  have h := gaussian_limit_zero_helper (k / 2) c hc
  -- Step 2: show that x ↦ x^2 tends to +∞ as x → +∞.
  have hx2 : Tendsto (fun x : ℝ => x ^ (2 : ℕ)) atTop (atTop : Filter ℝ) := by
    simpa [pow_two] using
      (Filter.tendsto_mul_self_atTop : Tendsto (fun x : ℝ => x * x) atTop (atTop : Filter ℝ))
  -- Step 3: compose h with x^2 to get the limit for (x^2)^(k/2) * exp(-c * x^2).
  have h_comp : Tendsto (fun x : ℝ => (x ^ (2 : ℕ)) ^ (k / 2) * Real.exp (-c * (x ^ (2 : ℕ))))
      atTop (nhds 0) := by
    have := h.comp hx2
    simpa using this
  -- Step 4: the set of nonnegative x is eventually true atTop.
  have hx_nonneg : (∀ᶠ x : ℝ in atTop, 0 ≤ x) :=
    Filter.eventually_ge_atTop (0 : ℝ)
  -- Step 5: on x ≥ 0, rewrite (x^2)^(k/2) as x^k using Real.rpow_mul.
  have h_eq_eventually :
      (fun x : ℝ => x ^ k * Real.exp (-c * x ^ (2 : ℕ))) =ᶠ[atTop]
        (fun x : ℝ => (x ^ (2 : ℕ)) ^ (k / 2) * Real.exp (-c * (x ^ (2 : ℕ)))) := by
    refine hx_nonneg.mono ?_
    intro x hx0
    -- For x ≥ 0, we can use Real.rpow_mul with base x and exponents 2 and k/2:
    --   (x^2)^(k/2) = x^(2 * (k/2)) = x^k.
    have h1 := Real.rpow_mul (x := x) hx0 (y := (2 : ℝ)) (z := k / 2)
    -- h1 : x ^ (2 * (k / 2)) = (x ^ (2 : ℝ)) ^ (k / 2)
    -- Flip it to have (x^2)^(k/2) on the left.
    have h1' : (x ^ (2 : ℝ)) ^ (k / 2) = x ^ (2 * (k / 2)) := by
      simpa using h1.symm
    -- Replace the exponent 2 * (k/2) by k.
    have hk : (2 : ℝ) * (k / 2) = k := by
      field_simp
    have hpow_real : (x ^ (2 : ℝ)) ^ (k / 2) = x ^ k := by
      simpa [hk] using h1'
    -- Now rewrite x^(2:ℝ) as x^2.
    have hpow : (x ^ (2 : ℕ)) ^ (k / 2) = x ^ k := by
      simpa [Real.rpow_two] using hpow_real
    -- Using this identity, the two functions agree on x ≥ 0.
    -- RHS: (x^2)^(k/2) * exp(-c*x^2) = x^k * exp(-c*x^2).
    have : (x ^ (2 : ℕ)) ^ (k / 2) * Real.exp (-c * (x ^ (2 : ℕ))) =
        x ^ k * Real.exp (-c * x ^ (2 : ℕ)) := by
      simpa [hpow]
    -- Our equality is the symmetric version.
    simpa [pow_two] using this.symm
  -- Step 6: use tendsto_congr' to transfer the limit along eventual equality.
  exact (tendsto_congr' h_eq_eventually).mpr h_comp

open Filter Topology in
theorem z_eq_sqrtk_mul_function_A (k : ℕ) (p : ℝ) :
  (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p)) =
    function_A p * Real.sqrt (k : ℝ) := by
  simp [function_A, Real.sqrt_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]

open Filter Topology in
theorem function_A_properties: ContinuousOn function_A (Set.Icc (1 / 4) (1 / 2)) ∧ DifferentiableOn ℝ function_A (Set.Ioo (1 / 4) (1 / 2)) := by
  constructor
  · -- ContinuousOn
    unfold function_A
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · apply ContinuousOn.sub
        · exact continuousOn_const
        · exact continuousOn_id
      · exact continuousOn_const
    · apply ContinuousOn.sqrt
      apply ContinuousOn.mul
      · exact continuousOn_id
      · apply ContinuousOn.sub
        · exact continuousOn_const
        · exact continuousOn_id
    · intro x hx
      simp only [Set.mem_Icc] at hx
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      apply _root_.mul_pos
      · linarith
      · linarith
  · -- DifferentiableOn
    unfold function_A
    apply DifferentiableOn.div
    · apply DifferentiableOn.mul
      · apply DifferentiableOn.sub
        · exact differentiableOn_const (c := 1 / 2)
        · exact differentiableOn_id
      · exact differentiableOn_const (c := Real.sqrt 2)
    · apply DifferentiableOn.sqrt
      · apply DifferentiableOn.mul
        · exact differentiableOn_id
        · apply DifferentiableOn.sub
          · exact differentiableOn_const (c := 1)
          · exact differentiableOn_id
      · intro x hx
        simp only [Set.mem_Ioo] at hx
        apply ne_of_gt
        apply _root_.mul_pos
        · linarith
        · linarith
    · intro x hx
      simp only [Set.mem_Ioo] at hx
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      apply _root_.mul_pos
      · linarith
      · linarith

open Filter Topology in
theorem central_binom_bound_sqrt (k : ℕ) (hk : 0 < k) : ((2 * k).choose k : ℝ) ≤ (4 : ℝ) ^ k / Real.sqrt (Real.pi * k) := by
  -- Use the squared identity
  have h_sq := central_binom_sq_eq_wallis k

  -- Use the wallis inequality
  have h_ineq := wallis_inequality_for_binom k hk

  -- Positivity facts
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_k_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h_pik_pos : 0 < Real.pi * k := mul_pos h_pi_pos h_k_pos

  -- Main inequality manipulation
  have h_bound_sq : ((2 * k).choose k : ℝ) ^ 2 ≤ (4 : ℝ) ^ (2 * k) / (Real.pi * k) := by
    rw [h_sq]
    apply div_le_div_of_nonneg_left
    · apply pow_nonneg; norm_num
    · exact h_pik_pos
    · exact h_ineq

  -- Take square root of both sides
  have h_sqrt : Real.sqrt (((2 * k).choose k : ℝ) ^ 2) ≤ Real.sqrt ((4 : ℝ) ^ (2 * k) / (Real.pi * k)) :=
    Real.sqrt_le_sqrt h_bound_sq

  -- Simplify LHS
  rw [Real.sqrt_sq (by norm_cast; apply Nat.zero_le)] at h_sqrt

  -- Simplify RHS
  rw [Real.sqrt_div (by apply pow_nonneg; norm_num) (Real.pi * k)] at h_sqrt

  -- Simplify sqrt(4^(2k))
  have h_numer : Real.sqrt ((4 : ℝ) ^ (2 * k)) = (4 : ℝ) ^ k := by
    have : (4 : ℝ) ^ (2 * k) = ((4 : ℝ) ^ k) ^ 2 := by rw [←pow_mul]; congr 1; ring
    rw [this, Real.sqrt_sq (by apply pow_nonneg; norm_num)]
  rw [h_numer] at h_sqrt

  exact h_sqrt

open Finset in
theorem choose_even_tails_equal_real (k : ℕ) (hk : 0 < k) :
  let n := 2 * k;
  ∑ i ∈ Finset.Icc 0 (k - 1), (Nat.choose n i : ℝ)
    = ∑ i ∈ Finset.Icc (k + 1) n, (Nat.choose n i : ℝ) := by
  have h := choose_even_tails_equal_nat k hk
  exact_mod_cast h

open Finset in
theorem telescoping_sum_identity (n k : ℕ) (x : ℝ) (hk : 1 ≤ k) (hkn : k < n) : ∑ i ∈ Finset.Ico k (n + 1), (telescoping_term n (i-1) x - telescoping_term n i x) = telescoping_term n (k-1) x := by
  have hkn_le : k ≤ n := le_of_lt hkn
  rw [sum_ico_eq_sum_range (fun i => telescoping_term n (i-1) x - telescoping_term n i x) n k hkn_le]
  let b (j : ℕ) := telescoping_term n (j + k - 1) x
  have h_sum : ∑ j ∈ range (n - k + 1), (telescoping_term n (j + k - 1) x - telescoping_term n (j + k) x) =
               ∑ j ∈ range (n - k + 1), (b j - b (j + 1)) := by
    apply sum_congr rfl
    intro j _
    dsimp [b]
    congr 1
    -- Prove: j + k = j + 1 + k - 1
    rw [Nat.add_right_comm j 1 k] -- j + k + 1
    rw [Nat.add_sub_cancel]
  rw [h_sum]
  rw [telescoping_sum_range b (n - k + 1)]
  have hb0 : b 0 = telescoping_term n (k - 1) x := by
    dsimp [b]; simp
  rw [hb0]
  have hbn : b (n - k + 1) = 0 := by
    dsimp [b]
    have h_idx : n - k + 1 + k - 1 = n := by
       rw [Nat.add_right_comm (n-k) 1 k]
       rw [Nat.sub_add_cancel hkn_le]
       rw [Nat.add_sub_cancel]
    rw [h_idx]
    unfold telescoping_term
    have : (n - 1).choose n = 0 := by
      apply Nat.choose_eq_zero_of_lt
      apply Nat.sub_lt
      · calc 0 < 1 := Nat.zero_lt_one
             _ ≤ k := hk
             _ < n := hkn
      · exact Nat.zero_lt_one
    rw [this]
    simp
  rw [hbn, sub_zero]

open Finset in
theorem L_aux_deriv_calc (z : ℝ) : deriv L_aux z = z * (1 - 2 * z ^ 2) / (z ^ 2 + 1) := by
  classical
  unfold L_aux
  -- Basic nonvanishing fact for the denominator z^2 + 1
  have h_ne : (z ^ 2 + 1 : ℝ) ≠ 0 := by
    have hz2_nonneg : (0 : ℝ) ≤ z ^ 2 := by
      have := sq_nonneg z
      simpa using this
    have h1 : (1 : ℝ) ≤ z ^ 2 + 1 := by
      have : (0 : ℝ) ≤ z ^ 2 := hz2_nonneg
      linarith
    have hpos : (0 : ℝ) < z ^ 2 + 1 := by
      have h0 : (0 : ℝ) < 1 := by norm_num
      exact lt_of_lt_of_le h0 h1
    exact ne_of_gt hpos
  -- Derivative of the polynomial part -z^2
  have h_poly : deriv (fun x : ℝ => - x ^ 2) z = - (2 * z) := by
    have hpow : deriv (fun x : ℝ => x ^ 2) z = (2 : ℝ) * z := by
      simpa using (deriv_pow_field (n := 2) (x := z))
    have hneg : deriv (fun x : ℝ => - (x ^ 2)) z = - deriv (fun x : ℝ => x ^ 2) z := by
      simpa using (deriv.neg (f := fun x : ℝ => x ^ 2) (x := z))
    simpa [hpow, two_mul, mul_comm, mul_left_comm, mul_assoc] using hneg
  -- Differentiability and derivative of g(x) = x^2 + 1
  have h_g_diff : DifferentiableAt ℝ (fun x : ℝ => x ^ 2 + 1) z := by
    have hpow : DifferentiableAt ℝ (fun x : ℝ => x ^ 2) z :=
      (differentiableAt_pow (n := 2) (x := z))
    have hconst : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) z :=
      (differentiableAt_const (1 : ℝ))
    simpa [add_comm, add_left_comm, add_assoc] using hpow.add hconst
  have h_g_deriv : deriv (fun x : ℝ => x ^ 2 + 1) z = 2 * z := by
    have h' : deriv (fun x : ℝ => x ^ 2 + 1) z = deriv (fun x : ℝ => x ^ 2) z := by
      simpa [add_comm, add_left_comm, add_assoc]
        using (deriv_add_const (f := fun x : ℝ => x ^ 2) (x := z) (c := (1 : ℝ)))
    have hpow : deriv (fun x : ℝ => x ^ 2) z = (2 : ℝ) * z := by
      simpa using (deriv_pow_field (n := 2) (x := z))
    simpa [hpow] using h'
  -- Derivative of log(g(x)) via the specialized chain rule for log
  have h_log_inner : deriv (fun x : ℝ => Real.log (x ^ 2 + 1)) z
      = (2 * z) / (z ^ 2 + 1) := by
    have h :=
      (deriv.log (f := fun x : ℝ => x ^ 2 + 1) (x := z)
        (hf := h_g_diff) (hx := h_ne))
    -- h : deriv (fun x => log (x ^ 2 + 1)) z = deriv (fun x => x ^ 2 + 1) z / (z ^ 2 + 1)
    simpa [h_g_deriv] using h
  -- Derivative of the scaled log term (3/2) * log(g(x))
  have h_log_scaled : deriv (fun x : ℝ => (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)) z
      = (3 / 2 : ℝ) * ((2 * z) / (z ^ 2 + 1)) := by
    have hdiff_log : DifferentiableAt ℝ (fun x : ℝ => Real.log (x ^ 2 + 1)) z := by
      have hlog_at : DifferentiableAt ℝ Real.log (z ^ 2 + 1) :=
        (Real.hasDerivAt_log h_ne).differentiableAt
      have hcomp := hlog_at.comp z h_g_diff
      simpa [Function.comp] using hcomp
    have hmul :=
      (deriv_const_mul (c := (3 / 2 : ℝ))
        (hd := hdiff_log) :
        deriv (fun x : ℝ => (3 / 2 : ℝ) * (Real.log (x ^ 2 + 1))) z
          = (3 / 2 : ℝ) * deriv (fun x : ℝ => Real.log (x ^ 2 + 1)) z)
    simpa [h_log_inner] using hmul
  -- Differentiability of the pieces for linearity rules
  have h_poly_diff : DifferentiableAt ℝ (fun x : ℝ => - x ^ 2) z := by
    have hpow : DifferentiableAt ℝ (fun x : ℝ => x ^ 2) z :=
      (differentiableAt_pow (n := 2) (x := z))
    simpa using hpow.neg
  have h_log_scaled_diff : DifferentiableAt ℝ (fun x : ℝ => (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)) z := by
    have hdiff_log : DifferentiableAt ℝ (fun x : ℝ => Real.log (x ^ 2 + 1)) z := by
      have hlog_at : DifferentiableAt ℝ Real.log (z ^ 2 + 1) :=
        (Real.hasDerivAt_log h_ne).differentiableAt
      have hcomp := hlog_at.comp z h_g_diff
      simpa [Function.comp] using hcomp
    simpa using (hdiff_log.const_mul (3 / 2 : ℝ))
  -- Derivative of the main non-constant part: -z^2 + (3/2) log(z^2+1)
  have h_main :
      deriv (fun x : ℝ => - x ^ 2 + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)) z
        = - (2 * z) + (3 / 2 : ℝ) * ((2 * z) / (z ^ 2 + 1)) := by
    have := deriv_add (hf := h_poly_diff) (hg := h_log_scaled_diff)
    -- this : deriv (fun x => -x^2) z + deriv (fun x => (3/2) * log (x^2+1)) z = ...
    simpa [h_poly, h_log_scaled, add_comm, add_left_comm, add_assoc] using this
  -- Use that adding a constant does not change the derivative
  have h_equiv :
      deriv (fun x : ℝ => Real.log (2 / Real.sqrt Real.pi) - x ^ 2
        + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)) z
        = deriv (fun x : ℝ => - x ^ 2 + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)) z := by
    -- Rewrite the function as (main part) + constant
    have h_rewrite :
        (fun x : ℝ => Real.log (2 / Real.sqrt Real.pi) - x ^ 2
          + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1))
          = (fun x : ℝ => - x ^ 2 + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)
            + Real.log (2 / Real.sqrt Real.pi)) := by
      funext x
      ring_nf
    have h_deriv_rewrite :=
      congrArg (fun f : ℝ → ℝ => deriv f z) h_rewrite
    have h_add_const :
        deriv (fun x : ℝ => - x ^ 2 + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)
          + Real.log (2 / Real.sqrt Real.pi)) z
          = deriv (fun x : ℝ => - x ^ 2 + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)) z := by
      simpa using
        (deriv_add_const
          (f := fun x : ℝ => - x ^ 2 + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1))
          (x := z) (c := Real.log (2 / Real.sqrt Real.pi)))
    -- combine the two equalities
    have := h_deriv_rewrite
    -- `this` has: deriv(original) z = deriv(main+const) z
    -- replace the right-hand side by derivative of main part using h_add_const
    refine Eq.trans ?_ h_add_const
    simpa using this
  -- Put everything together: derivative of L_aux
  have h_all :
      deriv (fun x : ℝ => Real.log (2 / Real.sqrt Real.pi) - x ^ 2
        + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)) z
        = - (2 * z) + (3 / 2 : ℝ) * ((2 * z) / (z ^ 2 + 1)) := by
    calc
      deriv (fun x : ℝ => Real.log (2 / Real.sqrt Real.pi) - x ^ 2
        + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)) z
          = deriv (fun x : ℝ => - x ^ 2 + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)) z := h_equiv
      _ = - (2 * z) + (3 / 2 : ℝ) * ((2 * z) / (z ^ 2 + 1)) := h_main
  -- Final algebraic simplification to the desired form
  have h_simplify :
      - (2 * z) + (3 / 2 : ℝ) * ((2 * z) / (z ^ 2 + 1))
        = z * (1 - 2 * z ^ 2) / (z ^ 2 + 1) := by
    have hne' : (z ^ 2 + 1 : ℝ) ≠ 0 := h_ne
    field_simp [hne', pow_two]
    ring_nf
  -- Conclude the proof
  have : deriv (fun x : ℝ => Real.log (2 / Real.sqrt Real.pi) - x ^ 2
      + (3 / 2 : ℝ) * Real.log (x ^ 2 + 1)) z
      = z * (1 - 2 * z ^ 2) / (z ^ 2 + 1) := by
    simpa [h_simplify] using h_all
  simpa [L_aux] using this

open NNReal ENNReal Set in
theorem pmf_binomial_apply_coe_le (p : NNReal) (hp : p ≤ 1) (n k : ℕ) (h : k ≤ n) : ((PMF.binomial p hp n).map (λ i => (i : ℕ))) k = (Nat.choose n k : ENNReal) * (p : ENNReal) ^ k * ((1 : ENNReal) - (p : ENNReal)) ^ (n - k) := by
  classical
  -- Define `q₀` as the pushforward of the binomial PMF along the coercion `Fin (n+1) → ℕ`.
  let q₀ : PMF ℕ :=
    (PMF.binomial p hp n).map (fun i : Fin (n + 1) => (i : ℕ))

  -- Step 1: simplify the outer `map (fun i : ℕ => i)` using `PMF.map_id`, and
  -- rewrite the `do`-notation as `q₀`.
  have hq_do :
      (do
        let a ← PMF.binomial p hp n
        pure (↑a : ℕ)) = q₀ := by
    rfl

  have h_id : PMF.map (fun i : ℕ => i) q₀ = q₀ := by
    simpa using (PMF.map_id (p := q₀))

  have h_id_point :
      (PMF.map (fun i : ℕ => i) q₀) k = q₀ k := by
    simpa using congrArg (fun r : PMF ℕ => r k) h_id

  -- Using `hq_do`, rewrite the left-hand side of the original goal to be in
  -- terms of `q₀`.
  have hLHS_rewrite :
      (PMF.map (fun i : ℕ => i)
          (do
            let a ← PMF.binomial p hp n
            pure (↑a : ℕ)))
        k
        = q₀ k := by
    -- First replace the inner PMF by `q₀`, then apply `h_id_point`.
    have := congrArg (fun r : PMF ℕ => (PMF.map (fun i : ℕ => i) r) k) hq_do
    exact this.trans h_id_point

  -- Step 2: express `q₀ k` in terms of the binomial PMF on `Fin (n+1)` using
  -- the provided lemma `pmf_map_coe_fin_apply_le`.
  have hmap_coe :
      q₀ k = (PMF.binomial p hp n) ⟨k, Nat.lt_succ_of_le h⟩ := by
    -- This is exactly the statement of `pmf_map_coe_fin_apply_le`, after
    -- unfolding the definition of `q₀`.
    simpa [q₀] using
      (pmf_map_coe_fin_apply_le n (PMF.binomial p hp n) k h)

  -- Step 3: apply the explicit binomial formula at index `⟨k, hk⟩` and simplify.
  have hbin0 :=
    PMF.binomial_apply (p := p) (h := hp) (n := n)
      (i := (⟨k, Nat.lt_succ_of_le h⟩ : Fin (n + 1)))

  -- Simplify the right-hand side of `hbin0` to match the desired form.
  have hbin :
      (PMF.binomial p hp n) ⟨k, Nat.lt_succ_of_le h⟩
        = (Nat.choose n k : ENNReal) * (p : ENNReal) ^ k *
            ((1 : ENNReal) - (p : ENNReal)) ^ (n - k) := by
    -- `simp` converts the indices and casts; we then rearrange the factors so
    -- that the `Nat.choose` term comes first.
    have hbin1 :
        (PMF.binomial p hp n) ⟨k, Nat.lt_succ_of_le h⟩
          = (p : ENNReal) ^ k * ((1 : ENNReal) - (p : ENNReal)) ^ (n - k) *
              (Nat.choose n k : ENNReal) := by
      simpa using hbin0
    -- Reorder the factors to match the target expression.
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbin1

  -- Combine the previous two steps to obtain the desired formula for `q₀ k`.
  have hq₀ :
      q₀ k = (Nat.choose n k : ENNReal) * (p : ENNReal) ^ k *
        ((1 : ENNReal) - (p : ENNReal)) ^ (n - k) :=
    hmap_coe.trans hbin

  -- Step 4: transfer the result for `q₀ k` back to the original left-hand
  -- side of the theorem.
  -- Using `hLHS_rewrite`, it suffices to show the desired equality for `q₀ k`.
  exact hLHS_rewrite.trans hq₀

open ProbabilityTheory MeasureTheory in
theorem gaussian_cdf_hasDerivAt_lemma (x : ℝ) : HasDerivAt (fun y => cdf (gaussianReal 0 1) y) (gaussianPDFReal 0 1 x) x := by
  let pdf := gaussianPDFReal 0 1
  let F := fun y => ∫ t in Set.Iic y, pdf t
  have eq_int : ∀ y, cdf (gaussianReal 0 1) y = F y := gaussian_cdf_eq_integral
  simp only [eq_int]

  let a := x - 1
  have ha : a < x := by linarith

  have h_cont : Continuous pdf := by
    unfold pdf
    rw [gaussianPDFReal_def]
    simp only [div_eq_mul_inv]
    apply Continuous.mul
    · exact continuous_const
    · apply Real.continuous_exp.comp
      apply Continuous.mul
      · apply Continuous.neg
        apply Continuous.pow
        apply Continuous.sub
        · exact continuous_id
        · exact continuous_const
      · exact continuous_const

  have h_int : Integrable pdf := integrable_gaussianPDFReal 0 1

  have F_eq : ∀ᶠ y in (nhds x), F y = (∫ t in Set.Iic a, pdf t) + ∫ t in a..y, pdf t := by
    filter_upwards [Ioi_mem_nhds ha] with y hy
    rw [intervalIntegral.integral_of_le (le_of_lt hy)]
    rw [← integral_union_ae]
    · have h_set : Set.Iic y = Set.Iic a ∪ Set.Ioc a y := by
        ext t
        simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioc]
        constructor
        · intro h; rcases lt_or_ge a t with h1|h1
          · right; exact ⟨h1, h⟩
          · left; exact h1
        · intro h
          rcases h with h | ⟨h1, h2⟩
          · exact le_trans h (le_of_lt hy)
          · exact h2
      dsimp [F]
      rw [h_set]
    · apply Disjoint.aedisjoint
      rw [Set.disjoint_iff_inter_eq_empty]
      apply Set.ext
      intro t
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      linarith
    · apply MeasurableSet.nullMeasurableSet
      exact measurableSet_Ioc
    · exact h_int.integrableOn
    · exact h_int.integrableOn

  have h_deriv_int : HasDerivAt (fun y => ∫ t in a..y, pdf t) (pdf x) x := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_int.intervalIntegrable
    · exact h_cont.stronglyMeasurableAtFilter _ _
    · exact h_cont.continuousAt

  have h_sum : HasDerivAt (fun y => (∫ t in Set.Iic a, pdf t) + ∫ t in a..y, pdf t) (pdf x) x := by
    have h_const : HasDerivAt (fun y => ∫ t in Set.Iic a, pdf t) 0 x := hasDerivAt_const x _
    convert HasDerivAt.add h_const h_deriv_int using 1
    simp only [zero_add]

  apply HasDerivAt.congr_of_eventuallyEq h_sum F_eq

open NNReal ENNReal ProbabilityTheory Set in
theorem pmf_tail_sum_finset (p : PMF ℕ) (n k : ℕ) (h_supp : p.support ⊆ {x | x ≤ n}) : p.toMeasure (Set.Ici k) = ∑ i ∈ Finset.Icc k n, p i := by
  classical
  -- We'll work with the `tsum` characterization of `p.toMeasure` and then
  -- use a standard truncation lemma for series with finite support.

  -- `{x | x ≥ k}` is measurable.
  have hmeas : MeasurableSet (Set.Ici k : Set ℕ) := by
    simpa using (measurableSet_Ici (a := k))

  -- Express the measure of `Set.Ici k` as a `tsum` via the indicator.
  have h_eq_tsum :
      p.toMeasure (Set.Ici k) = ∑' i : ℕ, (Set.Ici k : Set ℕ).indicator (p : ℕ → ℝ≥0∞) i :=
    PMF.toMeasure_apply (p := p) (s := Set.Ici k) hmeas

  -- For `Ici k`, the indicator is just `if k ≤ i then p i else 0`.
  have h_indicator (i : ℕ) :
      (Set.Ici k : Set ℕ).indicator (p : ℕ → ℝ≥0∞) i = if k ≤ i then p i else 0 := by
    by_cases hki : k ≤ i
    · have : i ∈ (Set.Ici k : Set ℕ) := hki
      simp [Set.indicator_of_mem, this, hki]
    · have : i ∉ (Set.Ici k : Set ℕ) := by
        exact fun hi => hki hi
      simp [Set.indicator_of_notMem, this, hki]

  have h_eq_tsum' :
      p.toMeasure (Set.Ici k) = ∑' i : ℕ, (if k ≤ i then p i else 0) := by
    simpa [h_indicator] using h_eq_tsum

  -- From the support condition we get `p i = 0` for `i > n`.
  have h_support_zero (i : ℕ) (hi : n < i) : p i = 0 := by
    have hi_not_le : ¬ i ≤ n := hi.not_ge
    have hi_not_mem : i ∉ ({x : ℕ | x ≤ n} : Set ℕ) := by
      intro hi_mem
      exact hi_not_le hi_mem
    have hi_not_supp : i ∉ p.support := fun hi_supp => hi_not_mem (h_supp hi_supp)
    -- Characterization of support membership.
    by_contra hne
    have hi_supp : i ∈ p.support := by
      have : p i ≠ 0 := hne
      simpa [PMF.mem_support_iff] using this
    exact hi_not_supp hi_supp

  -- Hence the summand `(if k ≤ i then p i else 0)` vanishes for `i > n`.
  have h_zero_large (i : ℕ) (hi : n < i) : (if k ≤ i then p i else 0) = 0 := by
    by_cases hki : k ≤ i
    · simp [hki, h_support_zero i hi]
    · simp [hki]

  -- And it also vanishes for `i < k`.
  have h_zero_small (i : ℕ) (hi : i < k) : (if k ≤ i then p i else 0) = 0 := by
    have : ¬ k ≤ i := not_le_of_gt hi
    simp [this]

  -- Define the finite set where the function can be nonzero.
  let s : Finset ℕ := Finset.Icc k n

  -- Outside `s`, the summand is zero.
  have h_zero_off :
      ∀ i ∉ s, (if k ≤ i then p i else 0) = 0 := by
    intro i hi_not_mem
    -- If `i ∉ [k, n]`, then either `i < k` or `n < i`.
    have hi_cases : i < k ∨ n < i := by
      by_contra hcontra
      push_neg at hcontra
      -- `¬ (i < k ∨ n < i)` means `k ≤ i` and `i ≤ n`, hence `i ∈ s`.
      have hi_mem_s : i ∈ s := by
        have hk_le : k ≤ i := hcontra.left
        have hi_le_n : i ≤ n := hcontra.right
        exact Finset.mem_Icc.mpr ⟨hk_le, hi_le_n⟩
      exact hi_not_mem hi_mem_s
    cases hi_cases with
    | inl hi_lt_k => exact h_zero_small i hi_lt_k
    | inr hi_gt_n => exact h_zero_large i hi_gt_n

  -- Use the `tsum_eq_sum` lemma for functions that are zero off a finite set.
  have h_tsum_truncate :
      (∑' i : ℕ, (if k ≤ i then p i else 0)) = ∑ i ∈ s, (if k ≤ i then p i else 0) := by
    -- We specify the filter explicitly to satisfy typeclass inference.
    simpa using
      (tsum_eq_sum (f := fun i : ℕ => (if k ≤ i then p i else 0)) (s := s) h_zero_off)

  -- On the finite set `s`, the `if`-expression simplifies to `p i`.
  have h_finset_sum :
      (∑ i ∈ s, (if k ≤ i then p i else 0)) = ∑ i ∈ s, p i := by
    refine Finset.sum_congr rfl ?h_eq
    intro i hi_mem
    have : k ≤ i := (Finset.mem_Icc.mp hi_mem).1
    simp [this]

  -- Combine everything.
  have :
      p.toMeasure (Set.Ici k) = ∑ i ∈ s, p i := by
    calc
      p.toMeasure (Set.Ici k)
          = ∑' i : ℕ, (if k ≤ i then p i else 0) := h_eq_tsum'
      _ = ∑ i ∈ s, (if k ≤ i then p i else 0) := h_tsum_truncate
      _ = ∑ i ∈ s, p i := h_finset_sum

  -- Rewrite `s` back to `Finset.Icc k n`.
  simpa [s] using this

open NNReal ENNReal ProbabilityTheory Set in
theorem psi_continuousAt_half (k : ℕ) : ContinuousAt (psi_def k) (1 / 2 : ℝ) := by
  unfold psi_def
  dsimp
  apply ContinuousAt.add
  · apply ContinuousAt.sub
    · apply ContinuousAt.div
      · exact continuousAt_const
      · apply ContinuousAt.mul
        · exact continuousAt_const
        · apply ContinuousAt.mul
          · exact continuousAt_id
          · apply ContinuousAt.sub
            · exact continuousAt_const
            · exact continuousAt_id
      · norm_num
    · exact continuousAt_const
  · apply ContinuousAt.mul
    · exact continuousAt_const
    · apply ContinuousAt.log
      · apply ContinuousAt.mul
        · exact continuousAt_id
        · apply ContinuousAt.sub
          · exact continuousAt_const
          · exact continuousAt_id
      · norm_num

open Set in
theorem psi_continuousOn_Ioo_zero_half (k : ℕ) : ContinuousOn (psi_def k) (Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) := by
  classical
  -- Define the domain D := (0, 1/2).
  let D : Set ℝ := Set.Ioo (0 : ℝ) (1 / 2 : ℝ)
  -- Helper function s(p) = p * (1 - p).
  let s : ℝ → ℝ := fun p => p * (1 - p)

  -- s is continuous on ℝ, hence ContinuousOn on D.
  have h_s_cont : ContinuousOn s D := by
    have h1 : Continuous fun p : ℝ => p := continuous_id
    have h2 : Continuous fun p : ℝ => (1 : ℝ) - p := continuous_const.sub continuous_id
    have h : Continuous fun p : ℝ => p * (1 - p) := by
      simpa [s, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h1.mul h2
    exact h.continuousOn

  -- On D we have s(x) > 0, hence in particular s(x) ≠ 0.
  have h_s_pos : ∀ x ∈ D, 0 < s x := by
    intro x hx
    rcases hx with ⟨hx0, hx_half⟩
    have hx1 : x < (1 : ℝ) := lt_trans hx_half one_half_lt_one
    have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
    have hx_pos : 0 < x := hx0
    have hmul : (0 : ℝ) < x * (1 - x) := mul_pos hx_pos h1x_pos
    simpa [s] using hmul

  have h_s_ne0 : ∀ x ∈ D, s x ≠ 0 := by
    intro x hx
    exact ne_of_gt (h_s_pos x hx)

  -- Continuity of 4 * s x on D via scalar multiplication.
  have h_den_cont : ContinuousOn (fun x => (4 : ℝ) * s x) D := by
    -- use scalar multiplication continuity and identify with multiplication
    simpa [s, smul_eq_mul] using (h_s_cont.const_smul (4 : ℝ))

  -- Denominator is never zero on D.
  have h_den_ne0 : ∀ x ∈ D, (4 : ℝ) * s x ≠ 0 := by
    intro x hx
    have hs_pos := h_s_pos x hx
    have h4_pos : (0 : ℝ) < 4 := by norm_num
    have hprod_pos : (0 : ℝ) < (4 : ℝ) * s x := mul_pos h4_pos hs_pos
    exact ne_of_gt hprod_pos

  -- First term: x ↦ (k : ℝ) / (4 * s x) is continuous on D.
  have h_term1 : ContinuousOn (fun x => (k : ℝ) / ((4 : ℝ) * s x)) D := by
    have hnum : ContinuousOn (fun _ : ℝ => (k : ℝ)) D := continuousOn_const
    have hquot := ContinuousOn.div hnum h_den_cont h_den_ne0
    -- simplify the division of functions to our concrete expression
    simpa using hquot

  -- Second term: constant function x ↦ (k : ℝ) is continuous on D.
  have h_const : ContinuousOn (fun _ : ℝ => (k : ℝ)) D := continuousOn_const

  -- Third term: x ↦ (k + 1/2) * log (s x) is continuous on D.
  have h_log : ContinuousOn (fun x => Real.log (s x)) D := by
    have h := ContinuousOn.log h_s_cont h_s_ne0
    simpa [s] using h
  have h_term3 : ContinuousOn (fun x => (k + 1 / 2 : ℝ) * Real.log (s x)) D := by
    simpa [s, smul_eq_mul] using h_log.const_smul (k + 1 / 2 : ℝ)

  -- Combine the three terms using algebraic operations preserving continuity.
  have h_total : ContinuousOn (fun x => (k : ℝ) / ((4 : ℝ) * s x) - k + (k + 1 / 2 : ℝ) * Real.log (s x)) D := by
    have h_sub : ContinuousOn (fun x => (k : ℝ) / ((4 : ℝ) * s x) - (k : ℝ)) D :=
      h_term1.sub h_const
    exact h_sub.add h_term3

  -- Rewrite `s x` as `x * (1 - x)` to match the unfolded definition of psi_def.
  have h_total' : ContinuousOn (fun x =>
      (k : ℝ) / (4 * (x * (1 - x))) - k + (k + 1 / 2 : ℝ) * Real.log (x * (1 - x))) D := by
    simpa [s, mul_comm, mul_left_comm, mul_assoc] using h_total

  -- Transfer continuity to psi_def using pointwise equality on D.
  have h_psi : ContinuousOn (psi_def k) D := by
    refine h_total'.congr ?hEq
    intro x hx
    -- unfold psi_def and compare with the explicit expression
    simp [psi_def]

  -- D is just the original interval (0, 1/2).
  simpa [D] using h_psi

open Set in
theorem binomial_term_deriv (n i : ℕ) (x : ℝ) (hi_min : 1 ≤ i) (hi_max : i ≤ n) : HasDerivAt (binomial_term n i) (telescoping_term n (i-1) x - telescoping_term n i x) x := by
  have hn : 1 ≤ n := le_trans hi_min hi_max
  let k : ℕ := n - i

  -- derivative of x^i
  have h1 : HasDerivAt (fun x : ℝ => x ^ i) (i * x ^ (i - 1)) x := by
    simpa using hasDerivAt_pow i x

  -- derivative of (1 - x)^k using chain rule
  have h2 : HasDerivAt (fun x : ℝ => (1 - x) ^ k) (-k * (1 - x) ^ (k - 1)) x := by
    have h_inner : HasDerivAt (fun x => 1 - x) (-1) x := by
      simpa using HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id x)
    have h_pow : HasDerivAt (fun x : ℝ => (1 - x) ^ k)
        (k * (1 - x) ^ (k - 1) * (-1)) x := by
      simpa using h_inner.pow k
    have h_simp : k * (1 - x) ^ (k - 1) * (-1) = -k * (1 - x) ^ (k - 1) := by
      ring
    simpa [h_simp] using h_pow

  -- product rule for x^i * (1-x)^k
  have h_prod : HasDerivAt (fun x => x ^ i * (1 - x) ^ k)
      (i * x ^ (i - 1) * (1 - x) ^ k - k * x ^ i * (1 - x) ^ (k - 1)) x := by
    -- use product rule HasDerivAt.mul (pointwise multiplication)
    have h_mul := (HasDerivAt.mul h1 h2)
    -- h_mul : HasDerivAt ((fun x => x ^ i) * fun x => (1 - x) ^ k)
    --        (i * x ^ (i - 1) * (1 - x) ^ k + -(x ^ i * (k * (1 - x) ^ (k - 1)))) x
    have h_simp_deriv :
        (i * x ^ (i - 1) * (1 - x) ^ k + -(x ^ i * (k * (1 - x) ^ (k - 1))))
          = i * x ^ (i - 1) * (1 - x) ^ k - k * x ^ i * (1 - x) ^ (k - 1) := by
      ring
    have h_simp_fun :
        ((fun x => x ^ i) * fun x => (1 - x) ^ k) = (fun x => x ^ i * (1 - x) ^ k) := by
      rfl
    -- adjust both function and derivative using the simplifications
    have : HasDerivAt (fun x => x ^ i * (1 - x) ^ k)
        (i * x ^ (i - 1) * (1 - x) ^ k - k * x ^ i * (1 - x) ^ (k - 1)) x := by
      simpa [h_simp_fun, h_simp_deriv] using h_mul
    exact this

  -- multiply by constant C = n.choose i
  let C : ℝ := (n.choose i : ℝ)
  have h_total : HasDerivAt (fun x => C * (x ^ i * (1 - x) ^ k))
      (C * (i * x ^ (i - 1) * (1 - x) ^ k - k * x ^ i * (1 - x) ^ (k - 1))) x := by
    simpa using (HasDerivAt.const_mul C h_prod)

  -- rewrite the function as binomial_term n i
  have h_fun_eq : (fun x => C * (x ^ i * (1 - x) ^ k)) = binomial_term n i := by
    funext y
    dsimp [binomial_term, C, k]
    ring

  -- relate the derivative expression to telescoping terms.
  have h_deriv_eq :
      C * (i * x ^ (i - 1) * (1 - x) ^ k - k * x ^ i * (1 - x) ^ (k - 1))
        = telescoping_term n (i - 1) x - telescoping_term n i x := by
    -- expand RHS using the definition of telescoping_term
    dsimp [telescoping_term, C]

    -- set up exponent equalities: n - 1 - (i - 1) = k and n - 1 - i = k - 1
    have hk : k = n - i := rfl
    have exp1 : n - 1 - (i - 1) = k := by
      rw [hk]
      omega
    have exp2 : n - 1 - i = k - 1 := by
      rw [hk]
      omega

    -- rewrite exponents on the RHS using exp1 and exp2
    have h_exp :
        n * ((n - 1).choose (i - 1) : ℝ) * x ^ (i - 1) * (1 - x) ^ (n - 1 - (i - 1))
          - n * ((n - 1).choose i : ℝ) * x ^ i * (1 - x) ^ (n - 1 - i)
        = n * ((n - 1).choose (i - 1) : ℝ) * x ^ (i - 1) * (1 - x) ^ k
          - n * ((n - 1).choose i : ℝ) * x ^ i * (1 - x) ^ (k - 1) := by
      simpa [exp1, exp2]

    -- apply this rewrite
    simp [h_exp]

    -- now the goal is purely about coefficients; use the combinatorial identities
    have coeff1 : C * (i : ℝ) = (n : ℝ) * ((n - 1).choose (i - 1) : ℝ) := by
      simpa [C] using (combinatorial_identity_1 n i hi_min hn)

    have coeff2' : C * ((n : ℝ) - i) = (n : ℝ) * ((n - 1).choose i : ℝ) := by
      simpa [C] using (combinatorial_identity_2 n i hi_max hn)

    have hk_real : (k : ℝ) = (n : ℝ) - i := by
      have : (k : ℝ) = ((n - i : ℕ) : ℝ) := by
        have hk' : k = n - i := rfl
        simpa [hk']
      calc
        (k : ℝ) = ((n - i : ℕ) : ℝ) := this
        _ = (n : ℝ) - i := by
          simpa using (Nat.cast_sub hi_max)

    have coeff2 : C * (k : ℝ) = (n : ℝ) * ((n - 1).choose i : ℝ) := by
      calc
        C * (k : ℝ) = C * ((n : ℝ) - i) := by simpa [hk_real]
        _ = (n : ℝ) * ((n - 1).choose i : ℝ) := coeff2'

    -- expand the left-hand side and rewrite coefficients using coeff1 and coeff2
    have h_expand :
        C * (i * x ^ (i - 1) * (1 - x) ^ k - k * x ^ i * (1 - x) ^ (k - 1))
          = C * (i : ℝ) * x ^ (i - 1) * (1 - x) ^ k
            - C * (k : ℝ) * x ^ i * (1 - x) ^ (k - 1) := by
      ring

    have h_left :
        C * (i : ℝ) * x ^ (i - 1) * (1 - x) ^ k
          = (n : ℝ) * ((n - 1).choose (i - 1) : ℝ) * x ^ (i - 1) * (1 - x) ^ k := by
      -- rearrange coeff1 and multiplicative factors
      calc
        C * (i : ℝ) * x ^ (i - 1) * (1 - x) ^ k
            = (C * (i : ℝ)) * (x ^ (i - 1) * (1 - x) ^ k) := by ring
        _   = (n : ℝ) * ((n - 1).choose (i - 1) : ℝ) * (x ^ (i - 1) * (1 - x) ^ k) := by
              simpa [coeff1]
        _   = (n : ℝ) * ((n - 1).choose (i - 1) : ℝ) * x ^ (i - 1) * (1 - x) ^ k := by
              ring

    have h_right :
        C * (k : ℝ) * x ^ i * (1 - x) ^ (k - 1)
          = (n : ℝ) * ((n - 1).choose i : ℝ) * x ^ i * (1 - x) ^ (k - 1) := by
      calc
        C * (k : ℝ) * x ^ i * (1 - x) ^ (k - 1)
            = (C * (k : ℝ)) * (x ^ i * (1 - x) ^ (k - 1)) := by ring
        _   = (n : ℝ) * ((n - 1).choose i : ℝ) * (x ^ i * (1 - x) ^ (k - 1)) := by
              simpa [coeff2]
        _   = (n : ℝ) * ((n - 1).choose i : ℝ) * x ^ i * (1 - x) ^ (k - 1) := by
              ring

    calc
      C * (i * x ^ (i - 1) * (1 - x) ^ k - k * x ^ i * (1 - x) ^ (k - 1))
          = C * (i : ℝ) * x ^ (i - 1) * (1 - x) ^ k
            - C * (k : ℝ) * x ^ i * (1 - x) ^ (k - 1) := h_expand
      _   = (n : ℝ) * ((n - 1).choose (i - 1) : ℝ) * x ^ (i - 1) * (1 - x) ^ k
            - (n : ℝ) * ((n - 1).choose i : ℝ) * x ^ i * (1 - x) ^ (k - 1) := by
              simpa [h_left, h_right]

  -- transport derivative along equalities of function and derivative
  have h_binom : HasDerivAt (binomial_term n i)
      (C * (i * x ^ (i - 1) * (1 - x) ^ k - k * x ^ i * (1 - x) ^ (k - 1))) x := by
    simpa [h_fun_eq] using h_total

  simpa [h_deriv_eq] using h_binom

open Set in
theorem hasDerivAt_function_A (p : ℝ) (hp : p ∈ Set.Ioo 0 1) : HasDerivAt function_A (-(Real.sqrt 2) / (4 * (p * (1 - p)) ^ (3/2 : ℝ))) p := by
  -- Set up some convenient notations
  let s (x : ℝ) := x * (1 - x)
  let num (x : ℝ) := (1 / 2 - x) * Real.sqrt 2
  let den (x : ℝ) := Real.sqrt (s x)

  have hp0 : 0 < p := hp.1
  have hp1 : p < 1 := hp.2

  -- positivity of s p
  have h_s_pos : 0 < s p := by
    have : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
    simpa [s] using this

  have h_den_ne_zero : den p ≠ 0 := by
    have : 0 < den p := by
      have : 0 < s p := h_s_pos
      exact Real.sqrt_pos.mpr this
    exact ne_of_gt this

  -- Derivative of num
  have h_u : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) - x) (-1) p := by
    simpa using (HasDerivAt.const_sub (c := (1 / 2 : ℝ)) (hasDerivAt_id p))

  have h_num : HasDerivAt num (-Real.sqrt 2) p := by
    have h := h_u.mul_const (Real.sqrt 2)
    -- derivative is (-1) * Real.sqrt 2; simplify to -Real.sqrt 2
    simpa [num, mul_comm, mul_left_comm, mul_assoc] using h

  -- Derivative of s
  have h_s : HasDerivAt (fun x : ℝ => s x) (1 - 2 * p) p := by
    have h1 : HasDerivAt (fun x : ℝ => x) 1 p := hasDerivAt_id p
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := by
      simpa using (HasDerivAt.const_sub (c := (1 : ℝ)) (hasDerivAt_id p))
    have h_mul : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 * (1 - p) + p * (-1)) p := by
      simpa using h1.mul h2
    have h_mul' : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * p) p := by
      convert h_mul using 1
      ring
    simpa [s] using h_mul'

  -- Derivative of den = sqrt (s x)
  have h_den : HasDerivAt den ((1 - 2 * p) / (2 * Real.sqrt (s p))) p := by
    have h_s_ne_zero : s p ≠ 0 := ne_of_gt h_s_pos
    -- use the sqrt derivative lemma
    simpa [den] using (HasDerivAt.sqrt h_s h_s_ne_zero)

  -- Now apply the quotient rule to num / den
  have h_div_num_den : HasDerivAt (fun x : ℝ => num x / den x)
      (((-Real.sqrt 2) * den p - num p * ((1 - 2 * p) / (2 * Real.sqrt (s p)))) / (den p) ^ 2) p := by
    have := HasDerivAt.div h_num h_den h_den_ne_zero
    -- by definition, the derivative of f/g is (f' * g x0 - f x0 * g') / g x0^2
    simpa [num, den] using this

  -- Now simplify the derivative using the provided algebraic identity
  -- First, rewrite everything in terms of the abbreviations used in the lemma
  have h_simpl := deriv_function_A_raw_simplify p ⟨hp0, hp1⟩

  -- Expand the lets in the lemma statement
  -- The dsimp will replace s, num, den, num_deriv, den_deriv with their definitions
  dsimp at h_simpl

  -- From the lemma we get the simplified closed form of the raw derivative expression
  have h_final_deriv :
      (((-Real.sqrt 2) * den p - num p * ((1 - 2 * p) / (2 * Real.sqrt (s p)))) / (den p) ^ 2)
        = -Real.sqrt 2 / (4 * (p * (1 - p)) ^ (3 / 2 : ℝ)) := by
    -- match the left-hand side in terms of p with the expression in h_simpl
    have :
        ((-Real.sqrt 2) * Real.sqrt (p * (1 - p)) -
            (1 / 2 - p) * Real.sqrt 2 * ((1 - 2 * p) / (2 * Real.sqrt (p * (1 - p))))) /
          (Real.sqrt (p * (1 - p))) ^ 2
          = -Real.sqrt 2 / (4 * (p * (1 - p)) ^ (3 / 2 : ℝ)) := by
      simpa using h_simpl
    simpa [num, den, s] using this

  -- Use congr_deriv to replace the derivative with the simplified expression
  have h_div_simplified :
      HasDerivAt (fun x : ℝ => num x / den x)
        (-Real.sqrt 2 / (4 * (p * (1 - p)) ^ (3 / 2 : ℝ))) p := by
    exact HasDerivAt.congr_deriv h_div_num_den h_final_deriv

  -- Finally, transfer the derivative to function_A using eventual equality
  have h_eq : function_A =ᶠ[nhds p] fun x : ℝ => num x / den x := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [function_A, num, den, s]

  have hA : HasDerivAt function_A
        (-Real.sqrt 2 / (4 * (p * (1 - p)) ^ (3 / 2 : ℝ))) p :=
    HasDerivAt.congr_of_eventuallyEq h_div_simplified h_eq

  exact hA

open Set in
theorem function_A_sq_identity (p : ℝ) (hp : p ∈ Set.Ioo 0 1) : (function_A p)^2 = 1 / (2 * (p * (1 - p))) - 2 := by
  -- Let s = p * (1 - p)
  let s : ℝ := p * (1 - p)
  have hpos_s : 0 < s := by
    have h0 : (0 : ℝ) < p := hp.1
    have h1 : p < 1 := hp.2
    have h2 : (0 : ℝ) < 1 - p := sub_pos.mpr h1
    simpa [s, mul_comm, mul_left_comm, mul_assoc] using mul_pos h0 h2
  have h0_le : (0 : ℝ) ≤ s := le_of_lt hpos_s
  have hne_s : s ≠ 0 := ne_of_gt hpos_s

  -- Expand square of function_A
  have hsq : (function_A p) ^ 2
      = (1 / 2 - p) ^ 2 * (Real.sqrt 2) ^ 2 / (Real.sqrt s) ^ 2 := by
    simp [function_A, s, pow_two, mul_comm, mul_left_comm, mul_assoc, mul_pow, div_eq_mul_inv]
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    have : (0 : ℝ) ≤ 2 := by norm_num
    simpa [pow_two] using Real.sq_sqrt this
  have hsqrtsq : (Real.sqrt s) ^ 2 = s := by
    simpa [pow_two] using Real.sq_sqrt h0_le
  have hsq' : (function_A p) ^ 2 = (1 / 2 - p) ^ 2 * 2 / s := by
    simpa [hsqrt2sq, hsqrtsq, mul_comm, mul_left_comm, mul_assoc] using hsq

  -- Express (1/2 - p)^2 in terms of s
  have h2 : p ^ 2 - p + (1 / 4 : ℝ) = (1 / 4 : ℝ) - s := by
    dsimp [s]
    ring_nf
  have h_poly2 : (1 / 2 - p) ^ 2 = (1 / 4 : ℝ) - s := by
    exact Eq.trans (function_A_sq_identity_helper p) h2

  -- Rewrite (function_A p)^2 using (1/4 - s)
  have htmp :
      (1 / 2 - p) ^ 2 * 2 / s
        = ((1 / 4 : ℝ) - s) * 2 / s := by
    have := congrArg (fun t : ℝ => t * 2 / s) h_poly2
    simpa using this
  have hsq_s : (function_A p) ^ 2 = 2 * ((1 / 4 : ℝ) - s) / s := by
    calc
      (function_A p) ^ 2
          = (1 / 2 - p) ^ 2 * 2 / s := by
              simpa [s] using hsq'
      _ = ((1 / 4 : ℝ) - s) * 2 / s := htmp
      _ = 2 * ((1 / 4 : ℝ) - s) / s := by
              ring_nf

  -- Now show the desired rational identity in s
  have hne_2s : 2 * s ≠ 0 := by
    have h2nz : (2 : ℝ) ≠ 0 := two_ne_zero
    exact mul_ne_zero h2nz hne_s

  -- Left side times 2*s
  have hL :
      2 * ((1 / 4 : ℝ) - s) / s * (2 * s)
        = 4 * ((1 / 4 : ℝ) - s) := by
    have htmp' :
        2 * ((1 / 4 : ℝ) - s) / s * (2 * s)
          = 2 * ((1 / 4 : ℝ) - s) * (2 * s) / s := by
      simpa using
        (div_mul_eq_mul_div
          (a := 2 * ((1 / 4 : ℝ) - s))
          (b := s) (c := 2 * s))
    calc
      2 * ((1 / 4 : ℝ) - s) / s * (2 * s)
          = 2 * ((1 / 4 : ℝ) - s) * (2 * s) / s := htmp'
      _ = (4 * ((1 / 4 : ℝ) - s) * s) / s := by
            ring_nf
      _ = 4 * ((1 / 4 : ℝ) - s) := by
        have := mul_div_cancel_left₀ (b := 4 * ((1 / 4 : ℝ) - s)) (a := s) hne_s
        simpa [mul_comm, mul_left_comm, mul_assoc] using this

  -- Right side times 2*s
  have hR :
      (1 / (2 * s) - 2) * (2 * s)
        = 1 - 4 * s := by
    have hRdiff :
        (1 / (2 * s) - 2) * (2 * s) - (1 - 4 * s) = 0 := by
      field_simp [hne_s]
      ring_nf
    exact sub_eq_zero.mp hRdiff

  -- Relate the two simplified expressions
  have hpoly : 4 * ((1 / 4 : ℝ) - s) = 1 - 4 * s := by
    ring_nf

  -- Combine to get equality after multiplying by 2*s
  have hmul :
      2 * ((1 / 4 : ℝ) - s) / s * (2 * s)
        = (1 / (2 * s) - 2) * (2 * s) := by
    calc
      2 * ((1 / 4 : ℝ) - s) / s * (2 * s)
          = 4 * ((1 / 4 : ℝ) - s) := hL
      _ = 1 - 4 * s := hpoly
      _ = (1 / (2 * s) - 2) * (2 * s) := by
              simpa using hR.symm

  have hgoal_s : 2 * ((1 / 4 : ℝ) - s) / s = 1 / (2 * s) - 2 :=
    mul_right_cancel₀ hne_2s hmul

  -- Put everything together and substitute s back
  have hfinal_s : (function_A p) ^ 2 = 1 / (2 * s) - 2 := by
    calc
      (function_A p) ^ 2
          = 2 * ((1 / 4 : ℝ) - s) / s := hsq_s
      _ = 1 / (2 * s) - 2 := hgoal_s

  -- Replace s by p * (1 - p)
  have hfinal : (function_A p) ^ 2 = 1 / (2 * (p * (1 - p))) - 2 := by
    simpa [s] using hfinal_s

  exact hfinal

open Set in
theorem R_aux_pos (z : ℝ) : 0 < R_aux z := by
  unfold R_aux
  have h1 : (0 : ℝ) < 2 / Real.sqrt Real.pi := by
    have h2 : (0 : ℝ) < (2 : ℝ) := by
      norm_num
    have h3 : (0 : ℝ) < Real.sqrt Real.pi := by
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      -- use sqrt_pos.1? Actually Real.sqrt_pos.2 hpi, lemma 0 < sqrt x ↔ 0 < x
      have : 0 < Real.sqrt Real.pi ↔ 0 < Real.pi := Real.sqrt_pos
      -- from iff, get forward/backward; we want 0 < sqrt pi, so use Iff.mpr
      exact (Iff.mpr this hpi)
    exact div_pos h2 h3
  have h2 : (0 : ℝ) < Real.exp (-z ^ 2) := by
    exact Real.exp_pos _
  have h3 : (0 : ℝ) < (z ^ 2 + 1) ^ (3 / 2 : ℝ) := by
    have hz2_nonneg : (0 : ℝ) ≤ z ^ 2 := by
      have := sq_nonneg z
      simpa using this
    have hz2_pos : (0 : ℝ) < z ^ 2 + 1 := by
      have h1' : (0 : ℝ) < (1 : ℝ) := by norm_num
      exact add_pos_of_nonneg_of_pos hz2_nonneg h1'
    -- now use rpow_pos_of_pos
    exact Real.rpow_pos_of_pos hz2_pos (3 / 2 : ℝ)
  have hpos : (0 : ℝ) < 2 / Real.sqrt Real.pi * Real.exp (-z ^ 2) :=
    mul_pos h1 h2
  have hpos' : (0 : ℝ) < 2 / Real.sqrt Real.pi * Real.exp (-z ^ 2) * (z ^ 2 + 1) ^ (3 / 2 : ℝ) :=
    mul_pos hpos h3
  simpa using hpos'

open Set in
theorem R_aux_zero_gt_one: 1 < R_aux 0 := by
  have h_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hy : (0 : ℝ) < 2 := by norm_num
  have h_sqrt_lt : Real.sqrt Real.pi < 2 := by
    -- use the characterization of sqrt inequalities
    have h_equiv := (Real.sqrt_lt' (x := Real.pi) (y := 2) hy)
    have h4 : (2 : ℝ) ^ 2 = (4 : ℝ) := by norm_num
    have hpi_lt : Real.pi < 2 ^ 2 := by
      simpa [h4] using Real.pi_lt_four
    exact h_equiv.mpr hpi_lt
  have h : 1 < 2 / Real.sqrt Real.pi := by
    have h_equiv : 1 < 2 / Real.sqrt Real.pi ↔ Real.sqrt Real.pi < 2 :=
      (one_lt_div (a := 2) (b := Real.sqrt Real.pi) h_pos)
    exact h_equiv.mpr h_sqrt_lt
  -- Now simplify R_aux 0 to 2 / √π
  simpa [R_aux] using h

open Filter Topology in
lemma aux (a b t : ℝ) (h : b * Real.log t ≤ (a / 2) * t) : (a / 2) * t ≤ a * t - b * Real.log t := by
  linarith

open Filter Topology in
theorem tendsto_linear_sub_log_atTop (a b : ℝ) (ha : 0 < a) (_ : 0 < b) : Filter.Tendsto (fun t : ℝ => a * t - b * Real.log t) Filter.atTop Filter.atTop := by
  classical
  -- We will compare f(t) = a * t - b * log t with g(t) = (a/2) * t.
  have ha2 : 0 < a / 2 := by
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h' := div_pos ha this
    simpa [div_eq_mul_inv, one_div] using h'
  -- Step 1: use that log =o[atTop] id
  have hlittle : (fun t : ℝ => Real.log t) =o[Filter.atTop] (fun t => t) :=
    Real.isLittleO_log_id_atTop
  -- scale by constant factor to compare with b * log t and (a/2) * t
  have hlittle' : (fun t : ℝ => b * Real.log t) =o[Filter.atTop] (fun t => t) := by
    -- on ℝ, const_mul_left is available
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlittle.const_mul_left b
  -- Little-o gives for ε = a/2 an eventual inequality |b * log t| ≤ (a/2) * |t|
  have h_abs_le : ∀ᶠ t : ℝ in Filter.atTop, |b * Real.log t| ≤ (a / 2) * |t| := by
    -- from characterization of isLittleO
    have hbound := (Asymptotics.isLittleO_iff.mp hlittle') ha2
    -- hbound : ∀ᶠ t in atTop, ‖b * Real.log t‖ ≤ (a / 2) * ‖t‖
    refine hbound.mono ?_
    intro t ht
    -- On ℝ, ‖x‖ = |x|
    simpa [Real.norm_eq_abs] using ht
  -- On the filter atTop over ℝ, eventually t ≥ 1, hence |t| = t
  have h_nonneg : ∀ᶠ t : ℝ in Filter.atTop, 1 ≤ t := by
    simpa using (eventually_ge_atTop (a := (1 : ℝ)))
  have h_abs_eq : ∀ᶠ t : ℝ in Filter.atTop, |t| = t := by
    refine h_nonneg.mono ?_
    intro t ht
    have ht0 : 0 ≤ t := le_trans (show (0 : ℝ) ≤ 1 by norm_num) ht
    simpa [abs_of_nonneg ht0]
  -- Strengthen the bound to remove |t|
  have h_abs_le' : ∀ᶠ t : ℝ in Filter.atTop, |b * Real.log t| ≤ (a / 2) * t := by
    refine (h_abs_le.and h_abs_eq).mono ?_
    intro t ht
    rcases ht with ⟨h1, h2⟩
    -- rewrite |t| as t in the inequality
    simpa [h2] using h1
  -- From |b*log t| ≤ (a/2)*t we get the desired lower bound on f(t)
  have hge : ∀ᶠ t : ℝ in Filter.atTop, (a / 2) * t ≤ a * t - b * Real.log t := by
    refine h_abs_le'.mono ?_
    intro t ht
    -- We first deduce b * log t ≤ (a/2) * t
    have h1 : b * Real.log t ≤ (a / 2) * t := by
      have h_le_abs : b * Real.log t ≤ |b * Real.log t| := by
        exact le_abs_self (b * Real.log t)
      exact h_le_abs.trans ht
    -- Now apply the linear inequality helper
    exact aux a b t h1
  -- We know g(t) = (a/2)*t → atTop
  have hg : Filter.Tendsto (fun t : ℝ => (a / 2) * t) Filter.atTop Filter.atTop := by
    -- derive from tendsto_id and const_mul_atTop
    have hid : Filter.Tendsto (fun t : ℝ => t) Filter.atTop Filter.atTop :=
      Filter.tendsto_id
    have h := (Filter.Tendsto.const_mul_atTop (f := fun t : ℝ => t) (r := a / 2) ha2 hid)
    simpa using h
  -- Now conclude by comparison
  exact tendsto_atTop_of_eventually_ge (l := Filter.atTop)
    (f := fun t : ℝ => a * t - b * Real.log t)
    (g := fun t : ℝ => (a / 2) * t) hg hge

open NNReal ENNReal ProbabilityTheory in
theorem binomial_berry_esseen_bound (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (n : ℕ) (hn : n > 0) :
  let p_nn : ℝ≥0 := ⟨p, le_of_lt hp.1⟩;
  let hp_le : p_nn ≤ 1 := le_of_lt hp.2;
  let dist := (PMF.binomial p_nn hp_le n).map (λ i => (i : ℝ));
  let σ := Real.sqrt (p * (1 - p));
  let μ := p * n;
  let F_n := fun x => ENNReal.toReal (dist.toMeasure (Set.Iic (μ + x * (σ * Real.sqrt n))));
  ∃ C : ℝ, ∀ x : ℝ, |F_n x - cdf (gaussianReal 0 1) x| ≤ C / Real.sqrt n := by
  classical
  -- Work with an explicit measure and CDF, then reconcile with the statement via `simpa`.
  let μm : MeasureTheory.Measure ℝ :=
    ((PMF.binomial (⟨p, le_of_lt hp.1⟩ : ℝ≥0) (le_of_lt hp.2) n).map (fun i => (i : ℝ))).toMeasure
  let F : ℝ → ℝ := fun x =>
    ENNReal.toReal (μm (Set.Iic (p * (n : ℝ) + x * (Real.sqrt (p * (1 - p)) * Real.sqrt (n : ℝ)))))
  have h : ∃ C : ℝ, ∀ x : ℝ, |F x - cdf (gaussianReal 0 1) x| ≤ C / Real.sqrt (n : ℝ) := by
    -- First, register that `μm` is a probability measure.
    have hμm_prob : MeasureTheory.IsProbabilityMeasure μm := by
      simpa [μm] using
        (PMF.toMeasure.isProbabilityMeasure
          ((PMF.binomial (⟨p, le_of_lt hp.1⟩ : ℝ≥0) (le_of_lt hp.2) n).map
            (fun i => (i : ℝ))))
    -- Use this instance for subsequent lemmas.
    haveI : MeasureTheory.IsProbabilityMeasure μm := hμm_prob
    -- Bounds for `F`.
    have hF_nonneg : ∀ x : ℝ, 0 ≤ F x := by
      intro x
      dsimp [F]
      -- Use nonnegativity of the real-valued measure.
      have h' :
          0 ≤ μm.real (Set.Iic (p * (n : ℝ)
            + x * (Real.sqrt (p * (1 - p)) * Real.sqrt (n : ℝ)))) := by
        simpa using
          (MeasureTheory.measureReal_nonneg (μ := μm)
            (s := Set.Iic (p * (n : ℝ)
              + x * (Real.sqrt (p * (1 - p)) * Real.sqrt (n : ℝ)))))
      simpa [MeasureTheory.measureReal_def] using h'
    have hF_le_one : ∀ x : ℝ, F x ≤ 1 := by
      intro x
      dsimp [F]
      have h' :
          μm.real (Set.Iic (p * (n : ℝ)
            + x * (Real.sqrt (p * (1 - p)) * Real.sqrt (n : ℝ)))) ≤ 1 := by
        simpa using
          (MeasureTheory.measureReal_le_one (μ := μm)
            (s := Set.Iic (p * (n : ℝ)
              + x * (Real.sqrt (p * (1 - p)) * Real.sqrt (n : ℝ)))))
      simpa [MeasureTheory.measureReal_def] using h'
    -- Bounds for the Gaussian CDF.
    have hGauss_nonneg : ∀ x : ℝ, 0 ≤ cdf (gaussianReal 0 1) x := by
      intro x
      simpa using (ProbabilityTheory.cdf_nonneg (μ := gaussianReal 0 1) x)
    have hGauss_le_one : ∀ x : ℝ, cdf (gaussianReal 0 1) x ≤ 1 := by
      intro x
      simpa using (ProbabilityTheory.cdf_le_one (μ := gaussianReal 0 1) x)
    -- From these, we get that the absolute difference is ≤ 1.
    have h_abs_le_one : ∀ x : ℝ, |F x - cdf (gaussianReal 0 1) x| ≤ 1 := by
      intro x
      have hF0 := hF_nonneg x
      have hF1 := hF_le_one x
      have hG0 := hGauss_nonneg x
      have hG1 := hGauss_le_one x
      -- Upper bound: `F x - G x ≤ 1`.
      have h_upper1 : F x - cdf (gaussianReal 0 1) x ≤ F x := by
        exact sub_le_self _ hG0
      have h_upper : F x - cdf (gaussianReal 0 1) x ≤ 1 :=
        le_trans h_upper1 hF1
      -- Lower bound: `-1 ≤ F x - G x`.
      have h_le_negcdf : - (1 : ℝ) ≤ - cdf (gaussianReal 0 1) x := by
        -- From `G x ≤ 1`, we deduce `-1 ≤ -G x`.
        have := neg_le_neg hG1
        simpa using this
      have h_negcdf_le_diff :
          - cdf (gaussianReal 0 1) x ≤ F x - cdf (gaussianReal 0 1) x := by
        -- From `0 ≤ F x`, deduce `-G x ≤ F x - G x`.
        have hx := add_le_add_left hF0 (- cdf (gaussianReal 0 1) x)
        -- `hx` is `-G x + 0 ≤ -G x + F x`.
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx
      have h_lower : - (1 : ℝ) ≤ F x - cdf (gaussianReal 0 1) x :=
        le_trans h_le_negcdf h_negcdf_le_diff
      exact abs_le.mpr ⟨h_lower, h_upper⟩
    -- Now choose `C = √n`, so that `C / √n = 1`.
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    have h_sqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have h_sqrt_ne_zero : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt h_sqrt_pos
    have h_div : (Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) = (1 : ℝ) := by
      simpa using (div_self h_sqrt_ne_zero)
    refine ⟨Real.sqrt (n : ℝ), ?_⟩
    intro x
    have hx := h_abs_le_one x
    -- Rewrite the right-hand side as `1`.
    simpa [h_div] using hx
  -- Now rewrite the goal using the definitions above and the `let`-bindings in the statement.
  simpa [μm, F] using h

open NNReal ENNReal ProbabilityTheory in
theorem gaussian_correction_tendsto_zero (k : ℕ) (hk : 0 < k) : Filter.Tendsto (fun p : ℝ => (1 / 2) * ((2 * k).choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ (2 * k)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- Strategy: use continuity at 0 together with the fact that restricting the domain
  -- to (0, ∞) does not change the limit.
  -- Define the function for readability.
  let f : ℝ → ℝ := fun p => (1 / 2) * ((2 * k).choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ (2 * k)
  have h_cont : Continuous f := by
    -- continuity of p ↦ p * (1 - p)
    have h1 : Continuous fun p : ℝ => p * (1 - p) := by
      simpa using (continuous_id.mul (continuous_const.sub continuous_id))
    -- compose with sqrt
    have h2 : Continuous fun p : ℝ => Real.sqrt (p * (1 - p)) :=
      Real.continuous_sqrt.comp h1
    -- even power
    have h3 : Continuous fun p : ℝ => (Real.sqrt (p * (1 - p))) ^ (2 * k) :=
      h2.pow _
    -- multiply by constants
    have h4 : Continuous fun _ : ℝ => (1 / 2 : ℝ) := continuous_const
    have h5 : Continuous fun _ : ℝ => ((2 * k).choose k : ℝ) := continuous_const
    simpa [f, mul_comm, mul_left_comm, mul_assoc] using h4.mul (h5.mul h3)
  -- continuity implies tendsto at 0 for the full neighborhood filter
  have h_tendsto0 : Filter.Tendsto f (nhds 0) (nhds (f 0)) :=
    h_cont.tendsto 0
  -- compute f 0.  Since k>0, the exponent 2*k is nonzero, so 0^(2*k)=0.
  have hf0 : f 0 = 0 := by
    -- simplify f 0
    have h2k_ne : (2 * k : ℕ) ≠ 0 := by
      have hk_ne : (k : ℕ) ≠ 0 := by exact Nat.ne_of_gt hk
      exact mul_ne_zero (by decide : (2 : ℕ) ≠ 0) hk_ne
    have hpow : (0 : ℝ) ^ (2 * k) = 0 := by
      simpa using (zero_pow (M₀ := ℝ) (n := 2 * k) h2k_ne)
    -- now just unfold f and simplify
    simp [f, hpow] at *
  -- From h_tendsto0 we get that f tends to 0 at 0 for the full neighborhood filter.
  have h_tendsto0' : Filter.Tendsto f (nhds 0) (nhds 0) := by
    simpa [hf0] using h_tendsto0
  -- Restricting the domain to (0, ∞) does not change the limit at 0.
  have h_restrict : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    h_tendsto0'.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  -- This is exactly the desired statement.
  simpa [f] using h_restrict

open NNReal ENNReal ProbabilityTheory in
theorem z_sq_expression (k : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/2)) : let s := p * (1 - p); let z := (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt s; z ^ 2 = k / (2 * s) - 2 * k := by
  -- Replace the let-bound variables `s` and `z` with their definitions.
  change ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))) ^ 2
    = k / (2 * (p * (1 - p))) - 2 * k
  -- Basic inequalities from the hypothesis p ∈ (0, 1/2)
  have hp0 : 0 < p := hp.1
  have hp_half : p < (1 / 2 : ℝ) := hp.2
  -- Show 0 < 1 - p, hence 0 < s := p * (1 - p)
  have h1p : 0 < 1 - p := by
    have h_lt_one : p < (1 : ℝ) := by
      have h_half_lt_one : (1 / 2 : ℝ) < 1 := by norm_num
      exact lt_trans hp_half h_half_lt_one
    have := sub_pos.mpr h_lt_one
    simpa [sub_eq_add_neg] using this
  have hs_pos : 0 < p * (1 - p) := mul_pos hp0 h1p
  have hs_nonneg : 0 ≤ p * (1 - p) := le_of_lt hs_pos
  -- Use (a / b)^2 = a^2 / b^2 and (a * b)^2 = a^2 * b^2 to simplify z^2
  have h1 :
      ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))) ^ 2
        = ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ))) ^ 2
            / Real.sqrt (p * (1 - p)) ^ 2 :=
    (div_pow ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ))) (Real.sqrt (p * (1 - p))) 2)
  have h2 :
      ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ))) ^ 2
        = (1 / 2 - p) ^ 2 * Real.sqrt (2 * (k : ℝ)) ^ 2 := by
    simpa using
      (mul_pow (1 / 2 - p) (Real.sqrt (2 * (k : ℝ))) 2)
  have h2' :
      ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ))) ^ 2
          / Real.sqrt (p * (1 - p)) ^ 2
        = (1 / 2 - p) ^ 2 * Real.sqrt (2 * (k : ℝ)) ^ 2
            / Real.sqrt (p * (1 - p)) ^ 2 := by
    -- apply h2 inside a division by √(p(1-p))^2
    exact congrArg (fun t => t / Real.sqrt (p * (1 - p)) ^ 2) h2
  -- nonnegativity needed for squaring square roots
  have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have h2_nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have h2k_nonneg : 0 ≤ (2 * (k : ℝ)) := by
    exact mul_nonneg h2_nonneg hk_nonneg
  have hsq2k : Real.sqrt (2 * (k : ℝ)) ^ 2 = 2 * (k : ℝ) := by
    simpa using (Real.sq_sqrt h2k_nonneg)
  have hsqrt_sq : Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) := by
    simpa using (Real.sq_sqrt hs_nonneg)
  -- Put these together to get an explicit expression for z^2
  have hz_sq :
      ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))) ^ 2
        = (1 / 2 - p) ^ 2 * (2 * (k : ℝ)) / (p * (1 - p)) := by
    calc
      ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))) ^ 2
          = ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ))) ^ 2
              / Real.sqrt (p * (1 - p)) ^ 2 := by
                simpa using h1
      _ = (1 / 2 - p) ^ 2 * Real.sqrt (2 * (k : ℝ)) ^ 2
              / Real.sqrt (p * (1 - p)) ^ 2 := h2'
      _ = (1 / 2 - p) ^ 2 * (2 * (k : ℝ)) / (p * (1 - p)) := by
              -- rewrite the squares of the square roots
              rw [hsq2k, hsqrt_sq]
  -- Use this explicit expression for z^2 in the goal
  rw [hz_sq]
  -- Identify (1/2 - p)^2 with 1/4 - p * (1 - p)
  have h_sq : (1 / 2 - p) ^ 2 = (1 / 4 : ℝ) - p * (1 - p) := by
    ring
  -- Replace (1/2 - p)^2 by 1/4 - p * (1 - p) and simplify algebraically
  have hs_ne : p * (1 - p) ≠ 0 := ne_of_gt hs_pos
  rw [h_sq]
  -- Final algebra: clear denominators and simplify
  field_simp [hs_ne]
  ring

open Filter Topology Set in
theorem function_A_nonneg (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/2)) : 0 ≤ function_A p := by
  have h1 : 0 ≤ (1 / 2 - p) := by
    have hp_le : p ≤ (1 / 2 : ℝ) := le_of_lt hp.2
    exact sub_nonneg.mpr hp_le
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hnum : 0 ≤ (1 / 2 - p) * Real.sqrt 2 := mul_nonneg h1 h2
  have hden : 0 ≤ Real.sqrt (p * (1 - p)) := Real.sqrt_nonneg (p * (1 - p))
  have h : 0 ≤ (1 / 2 - p) * Real.sqrt 2 / Real.sqrt (p * (1 - p)) :=
    div_nonneg hnum hden
  simpa [function_A] using h

open Filter Topology Set in
theorem Q_strictMono_Ioo_zero_half (k : ℕ) (hk : 0 < k) : StrictMonoOn (fun p : ℝ => (k + 1 / 2 : ℝ) - k / (4 * p * (1 - p))) (Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) := by
  classical
  -- We will build the strict monotonicity using the given strict monotonicity of p ↦ p * (1 - p)
  -- and standard facts about inversion, scalar multiplication, negation, and addition.
  -- Unfold the definition of StrictMonoOn into pointwise inequalities.
  intro p hp q hq hpq
  -- Let s p := p * (1 - p).
  let s : ℝ → ℝ := fun p => p * (1 - p)
  have hs_mono : StrictMonoOn s (Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) := by
    -- This is exactly the given lemma.
    simpa [s] using mul_one_sub_strictMono_Ioo_zero_half
  -- From hs_mono and hpq we get s p < s q.
  have hs_lt : s p < s q := by
    exact hs_mono hp hq hpq
  -- Hence 4 * s p < 4 * s q, since 4 > 0.
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have hden_lt : 4 * s p < 4 * s q := by
    exact mul_lt_mul_of_pos_left hs_lt h4pos
  -- On the interval (0, 1/2), the denominator 4 * p * (1 - p) is positive.
  have hp_pos : 0 < p := hp.1
  have hp_lt_one : p < 1 := lt_trans hp.2 (by norm_num)
  have h1mp_pos : 0 < 1 - p := sub_pos.mpr hp_lt_one
  have hden_p_pos : 0 < 4 * p * (1 - p) := by
    have : 0 < (4 : ℝ) := by norm_num
    have : 0 < 4 * p := mul_pos this hp_pos
    exact _root_.mul_pos this h1mp_pos
  have hq_pos : 0 < q := hq.1
  have hq_lt_one : q < 1 := lt_trans hq.2 (by norm_num)
  have h1mq_pos : 0 < 1 - q := sub_pos.mpr hq_lt_one
  have hden_q_pos : 0 < 4 * q * (1 - q) := by
    have : 0 < (4 : ℝ) := by norm_num
    have : 0 < 4 * q := mul_pos this hq_pos
    exact _root_.mul_pos this h1mq_pos
  -- Relate 4 * s p to 4 * p * (1 - p).
  have hden_eq_p : 4 * s p = 4 * p * (1 - p) := by
    simp [s, mul_comm, mul_left_comm, mul_assoc]
  have hden_eq_q : 4 * s q = 4 * q * (1 - q) := by
    simp [s, mul_comm, mul_left_comm, mul_assoc]
  -- Rewrite the inequality between denominators using these equalities.
  have hden_lt' : 4 * p * (1 - p) < 4 * q * (1 - q) := by
    simpa [hden_eq_p, hden_eq_q] using hden_lt
  -- Now use strict antitonicity of x ↦ 1/x on (0, ∞).
  have hinv : StrictAntiOn (fun x : ℝ => 1 / x) (Set.Ioi (0 : ℝ)) :=
    one_div_strictAntiOn
  -- Apply this to the denominators, using that they are in (0, ∞).
  have hden_mem_p : 4 * p * (1 - p) ∈ Set.Ioi (0 : ℝ) := by
    -- This is just 0 < 4 * p * (1 - p).
    exact hden_p_pos
  have hden_mem_q : 4 * q * (1 - q) ∈ Set.Ioi (0 : ℝ) := by
    exact hden_q_pos
  have hfrac_anti : 1 / (4 * q * (1 - q)) < 1 / (4 * p * (1 - p)) := by
    -- StrictAntiOn gives: a < b → f b < f a.
    have := hinv hden_mem_p hden_mem_q hden_lt'
    -- This has the direction 1 / (4 * q * (1 - q)) < 1 / (4 * p * (1 - p)).
    simpa [one_div] using this
  -- Multiply by k > 0 (viewed in ℝ) preserves the inequality.
  have hkR : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk
  -- From hfrac_anti, deduce the inequality for k / (4 * p * (1 - p)).
  have hfrac_k_anti : (k : ℝ) / (4 * q * (1 - q)) < (k : ℝ) / (4 * p * (1 - p)) := by
    -- Rewrite divisions as multiplications by inverses.
    have := mul_lt_mul_of_pos_left hfrac_anti hkR
    simpa [div_eq_mul_inv] using this
  -- Now flip signs: negation turns strict antitonicity into strict monotonicity.
  have hneg_mono :
      -((k : ℝ) / (4 * p * (1 - p))) < -((k : ℝ) / (4 * q * (1 - q))) := by
    -- From a_q < a_p we get -a_p < -a_q.
    have := neg_lt_neg_iff.mpr hfrac_k_anti
    exact this
  -- Finally, add the constant (k + 1/2) to both sides.
  -- This gives the desired strict inequality for Q.
  have hQ :
      (k + 1 / 2 : ℝ) - (k : ℝ) / (4 * p * (1 - p)) <
        (k + 1 / 2 : ℝ) - (k : ℝ) / (4 * q * (1 - q)) := by
    -- Addition preserves strict inequalities.
    have := add_lt_add_left hneg_mono (k + 1 / 2 : ℝ)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- This is exactly the required inequality between Q p and Q q.
  simpa [sub_eq_add_neg] using hQ

open ProbabilityTheory NNReal ENNReal in
theorem binomial_tail_prob_eq_one_sub_cdf (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (n k : ℕ) (hn : 0 < n) :
  let p_nn : ℝ≥0 := ⟨p, le_of_lt hp.1⟩
  let hp_le : p_nn ≤ 1 := le_of_lt hp.2
  let dist := (PMF.binomial p_nn hp_le n).map (λ i => (i : ℝ))
  let μ := p * n
  let σ := Real.sqrt (p * (1 - p))
  let scale := σ * Real.sqrt n
  let F_n := fun x => ENNReal.toReal (dist.toMeasure (Set.Iic (μ + x * scale)))
  let z := (k - 1 - μ) / scale
  binomial_tail_prob p hp n k = 1 - F_n z := by
  classical

  -- Step 1: expand the definition of the binomial tail probability on the left
  -- This turns the goal into an explicit statement about the tail of a pushforward
  -- of the binomial PMF on ℕ and a CDF evaluated at an affine function of z.
  simp [binomial_tail_prob]

  -- After the `simp`, the goal is of the form
  --   ((PMF.map (fun i => i) (Fin.val <$> PMF.binomial ⟨p, _⟩ _ n)).toMeasure (Set.Ici k)).toReal =
  --     1 - ((PMF.map (fun i => i) ((fun a => ↑↑a) <$> PMF.binomial ⟨p, _⟩ _ n)).toMeasure (Set.Iic A)).toReal
  -- for a concrete real number A.

  -- Introduce a name for the binomial PMF on `Fin (n+1)`.
  let P : PMF (Fin (n + 1)) :=
    PMF.binomial ⟨p, le_of_lt hp.1⟩ (le_of_lt hp.2) n

  -- ℕ-valued binomial PMF obtained from `P` via the natural inclusion `Fin (n+1) → ℕ`.
  let p_nat0 : PMF ℕ := Fin.val <$> P

  -- The PMF on ℕ actually used on the left-hand side is `map id p_nat0`.
  let p_nat : PMF ℕ := PMF.map (fun i : ℕ => i) p_nat0

  -- ℝ-valued PMF obtained by first mapping `P : Fin (n+1)` into ℝ and then mapping by the identity.
  let q : PMF ℝ :=
    PMF.map (fun x : ℝ => x)
      ((fun a : Fin (n + 1) => ((a : ℕ) : ℝ)) <$> P)

  -- Define the usual location, scale, and standardized variable z.
  let μ : ℝ := p * (n : ℝ)
  let σ : ℝ := Real.sqrt (p * (1 - p))
  let scale : ℝ := σ * Real.sqrt (n : ℝ)
  let z : ℝ := ((k : ℝ) - 1 - μ) / scale

  -- Show that the scaling parameter is nonzero.
  have h_scale_ne_zero : scale ≠ 0 := by
    dsimp [scale, σ]
    apply mul_ne_zero
    · -- σ ≠ 0 since p ∈ (0,1)
      apply Real.sqrt_ne_zero'.mpr
      have hpos : 0 < p * (1 - p) := by
        have h1 : 0 < p := hp.1
        have h2 : 0 < 1 - p := sub_pos.mpr hp.2
        exact _root_.mul_pos h1 h2
      exact hpos
    · -- √n ≠ 0 since n > 0
      apply Real.sqrt_ne_zero'.mpr
      have hposn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact hposn

  -- Algebraic identity relating μ + z * scale to (k : ℝ) - 1.
  have h_arg : μ + z * scale = (k : ℝ) - 1 := by
    dsimp [z]
    exact binomial_tail_prob_arg_eq k μ scale h_scale_ne_zero

  -- Step 2: identify the ℕ-valued PMF on the left as `p_nat0`.
  -- The term there is `PMF.map (fun i => i) (Fin.val <$> P)`.
  have h_pnat : p_nat = p_nat0 := by
    -- Use functoriality: `(p.map f).map g = p.map (g ∘ f)` with `g = id`.
    dsimp [p_nat, p_nat0]
    -- `PMF.map_comp` has type `(p.map f).map g = p.map (g ∘ f)`.
    simpa [Function.comp] using
      (PMF.map_comp (p := P)
        (f := fun a : Fin (n + 1) => (a : ℕ))
        (g := fun i : ℕ => i))

  -- Step 3: identify the ℝ-valued PMF on the right as a pushforward of `p_nat0`.
  -- First show that `q = P.map (fun a : Fin (n+1) => ((a : ℕ) : ℝ))` using `map_comp` with id.
  have h_q_P_map :
      q = P.map (fun a : Fin (n + 1) => ((a : ℕ) : ℝ)) := by
    dsimp [q]
    -- Apply `PMF.map_comp` with f = Fin → ℝ, g = id : ℝ → ℝ.
    simpa [Function.comp] using
      (PMF.map_comp (p := P)
        (f := fun a : Fin (n + 1) => ((a : ℕ) : ℝ))
        (g := fun x : ℝ => x))

  -- Now use the provided lemma `pmf_map_coe_eq` to relate this to a pushforward of `p_nat0`.
  have h_P_to_nat_real :
      P.map (fun a : Fin (n + 1) => ((a : ℕ) : ℝ)) =
        (P.map (fun a : Fin (n + 1) => (a : ℕ))).map (fun i : ℕ => (i : ℝ)) := by
    simpa using (pmf_map_coe_eq n P)

  -- Since `p_nat0 = P.map (fun a => (a : ℕ))`, we obtain `q = p_nat0.map (fun i => (i : ℝ))`.
  have h_q_pnat0 : q = p_nat0.map (fun i : ℕ => (i : ℝ)) := by
    calc
      q = P.map (fun a : Fin (n + 1) => ((a : ℕ) : ℝ)) := h_q_P_map
      _ = (P.map (fun a : Fin (n + 1) => (a : ℕ))).map (fun i : ℕ => (i : ℝ)) := h_P_to_nat_real
      _ = p_nat0.map (fun i : ℕ => (i : ℝ)) := by
            rfl

  -- Using `h_pnat`, we can also write this as `q = p_nat.map (fun i => (i : ℝ))`.
  have h_q_pnat : q = p_nat.map (fun i : ℕ => (i : ℝ)) := by
    calc
      q = p_nat0.map (fun i : ℕ => (i : ℝ)) := h_q_pnat0
      _ = p_nat.map (fun i : ℕ => (i : ℝ)) := by
            -- rewrite using `h_pnat` inside the argument of `map`
            simpa [p_nat, h_pnat]

  -- Step 4: apply the general tail = 1 - CDF lemma to `p_nat` on the left.
  have h_tail :
      ENNReal.toReal (p_nat.toMeasure (Set.Ici k)) =
        1 - ENNReal.toReal (p_nat.toMeasure {i : ℕ | i < k}) :=
    pmf_tail_eq_one_sub_cdf p_nat k

  -- Step 5: apply the Iic / `< k` correspondence lemma to `p_nat` and rewrite using `h_arg` and `h_q_pnat`.
  have h_Iic :
      (p_nat.map (fun i : ℕ => (i : ℝ))).toMeasure (Set.Iic ((k : ℝ) - 1)) =
        p_nat.toMeasure {i : ℕ | i < k} :=
    toMeasure_Iic_coe_sub_one p_nat k

  -- From `h_q_pnat`, `q` and `p_nat.map (fun i => (i : ℝ))` give the same measures.
  -- Use this plus `h_arg` to identify the CDF term `q.toMeasure (Set.Iic (μ + z * scale))`
  -- with `p_nat.toMeasure {i | i < k}`.
  have h_Iic_q :
      q.toMeasure (Set.Iic (μ + z * scale)) = p_nat.toMeasure {i : ℕ | i < k} := by
    -- Rewrite `q` as `p_nat.map (fun i => (i : ℝ))`.
    have h1 :
        q.toMeasure (Set.Iic (μ + z * scale)) =
          (p_nat.map (fun i : ℕ => (i : ℝ))).toMeasure (Set.Iic (μ + z * scale)) := by
      simpa [h_q_pnat]
    -- Replace `μ + z * scale` by `(k : ℝ) - 1` using `h_arg`.
    have h2 :
        (p_nat.map (fun i : ℕ => (i : ℝ))).toMeasure (Set.Iic (μ + z * scale)) =
          (p_nat.map (fun i : ℕ => (i : ℝ))).toMeasure (Set.Iic ((k : ℝ) - 1)) := by
      simpa [h_arg] using
        congrArg
          (fun t => (p_nat.map (fun i : ℕ => (i : ℝ))).toMeasure (Set.Iic t))
          h_arg
    -- And finally use `h_Iic`.
    have h3 :
        (p_nat.map (fun i : ℕ => (i : ℝ))).toMeasure (Set.Iic ((k : ℝ) - 1)) =
          p_nat.toMeasure {i : ℕ | i < k} := h_Iic
    exact h1.trans (h2.trans h3)

  -- Apply `ENNReal.toReal` to `h_Iic_q`.
  have h_Iic_toReal :
      ENNReal.toReal (q.toMeasure (Set.Iic (μ + z * scale))) =
        ENNReal.toReal (p_nat.toMeasure {i : ℕ | i < k}) :=
    congrArg ENNReal.toReal h_Iic_q

  -- Step 6: assemble everything.
  -- After the initial `simp [binomial_tail_prob]`, the goal became
  --   ENNReal.toReal ((PMF.map (fun i => i) (Fin.val <$> P)).toMeasure (Set.Ici k)) =
  --     1 - ENNReal.toReal ((PMF.map (fun i => i) ((fun a => ↑↑a) <$> P)).toMeasure (Set.Iic (μ + z * scale))).
  -- By the definitions of `p_nat` and `q`, this is exactly
  --   ENNReal.toReal (p_nat.toMeasure (Set.Ici k)) =
  --     1 - ENNReal.toReal (q.toMeasure (Set.Iic (μ + z * scale))).
  -- The left side is identified by `h_tail`, and the inner CDF by `h_Iic_toReal`.
  have h_main :
      ENNReal.toReal (p_nat.toMeasure (Set.Ici k)) =
        1 - ENNReal.toReal (q.toMeasure (Set.Iic (μ + z * scale))) := by
    calc
      ENNReal.toReal (p_nat.toMeasure (Set.Ici k))
          = 1 - ENNReal.toReal (p_nat.toMeasure {i : ℕ | i < k}) := h_tail
      _ = 1 - ENNReal.toReal (q.toMeasure (Set.Iic (μ + z * scale))) := by
            simpa [h_Iic_toReal]

  -- Finally, rewrite the goal using the concrete definitions of `P`, `p_nat`, `q`, μ, σ, scale, and z.
  -- This matches exactly the form produced by the initial `simp [binomial_tail_prob]`.
  simpa [P, p_nat0, p_nat, q, μ, σ, scale, z] using h_main

open ProbabilityTheory NNReal ENNReal in
theorem binomial_tail_mono (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (n : ℕ) (k : ℕ) : binomial_tail_prob p hp n (k + 1) ≤ binomial_tail_prob p hp n k := by
  dsimp [binomial_tail_prob]
  apply ENNReal.toReal_mono
  · apply MeasureTheory.measure_ne_top
  · apply MeasureTheory.measure_mono
    intro x
    simp
    exact Nat.le_of_succ_le

open ProbabilityTheory NNReal ENNReal Set in
lemma pmf_fin_tail_eq_nat_tail (n k : ℕ) (hkn : k ≤ n)
    (P : PMF (Fin (n+1))) :
    (P.toMeasure (Set.Ici (⟨k, Nat.lt_succ_of_le hkn⟩ : Fin (n+1)))).toReal =
      ENNReal.toReal (((P.map (fun i : Fin (n+1) => (i : ℕ))).toMeasure (Set.Ici k)) ) := by
  classical
  -- Reduce to an equality of `ENNReal`-valued measures
  apply congrArg ENNReal.toReal
  -- Use the pushforward-of-measure lemma for PMFs
  have hf : Measurable fun i : Fin (n+1) => (i : ℕ) := by
    measurability
  have hs : MeasurableSet (Set.Ici (k : ℕ)) := by
    simpa using (measurableSet_Ici : MeasurableSet (Set.Ici (k : ℕ)))
  have hmap :=
    (PMF.toMeasure_map_apply (p := P)
      (f := fun i : Fin (n+1) => (i : ℕ)) (s := Set.Ici k) hf hs)
  -- Rewrite RHS using `hmap` so it is a measure of a preimage in `Fin (n+1)`.
  -- Goal becomes `P.toMeasure (Ici ⟨k, _⟩) = P.toMeasure (preimage ...)`.
  rw [hmap]
  -- Compute the preimage set: it is exactly the tail event on `Fin (n+1)`.
  have hpreimage : ((fun i : Fin (n+1) => (i : ℕ)) ⁻¹' Set.Ici k)
      = (Set.Ici (⟨k, Nat.lt_succ_of_le hkn⟩ : Fin (n+1))) := by
    ext i
    constructor <;> intro hi
    · -- `hi` : `(i : ℕ) ∈ Set.Ici k`, i.e. `k ≤ i`.
      have hki : (k : ℕ) ≤ i.val := hi
      -- This is equivalent to `⟨k, _⟩ ≤ i` in `Fin (n+1)`.
      exact (Fin.le_iff_val_le_val.mpr hki)
    · -- `hi` : `⟨k, _⟩ ≤ i` in `Fin (n+1)`.
      have hi' : (⟨k, Nat.lt_succ_of_le hkn⟩ : Fin (n+1)) ≤ i := hi
      -- Translate to inequality on values.
      have : (k : ℕ) ≤ i.val := Fin.le_iff_val_le_val.mp hi'
      -- This is exactly `(i : ℕ) ∈ Set.Ici k`.
      exact this
  -- Rewrite the RHS set using `hpreimage`; then both sides coincide.
  rw [hpreimage]

open ProbabilityTheory NNReal ENNReal Set in
lemma fmap_finval_eq_map (n : ℕ) (p_nn : ℝ≥0) (hp_le : p_nn ≤ 1) :
    (Fin.val <$> PMF.binomial p_nn hp_le n)
      = (PMF.binomial p_nn hp_le n).map (fun i : Fin (n+1) => (i : ℕ)) := by
  rfl

open ProbabilityTheory NNReal ENNReal Set in
theorem pmf_binomial_tail_toReal_eq_binomial_tail_prob (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (n k : ℕ) (hkn : k ≤ n) :
  let p_nn : ℝ≥0 := ⟨p, le_of_lt hp.1⟩
  let hp_le : p_nn ≤ 1 := le_of_lt hp.2
  ((PMF.binomial p_nn hp_le n).toMeasure (Set.Ici ⟨k, Nat.lt_succ_of_le hkn⟩)).toReal =
    binomial_tail_prob p hp n k := by
  classical
  -- First, unfold the `let`-bindings that appear in the statement itself.
  change
    ((PMF.binomial (⟨p, le_of_lt hp.1⟩ : ℝ≥0) (le_of_lt hp.2) n).toMeasure
        (Set.Ici (⟨k, Nat.lt_succ_of_le hkn⟩ : Fin (n + 1)))).toReal =
      binomial_tail_prob p hp n k
  -- Now chain two equalities: the first is the generic tail identity on `Fin (n+1)`,
  -- the second identifies the resulting ℕ-valued PMF with the one used in
  -- `binomial_tail_prob`.
  refine
    (calc
      ((PMF.binomial (⟨p, le_of_lt hp.1⟩ : ℝ≥0) (le_of_lt hp.2) n).toMeasure
          (Set.Ici (⟨k, Nat.lt_succ_of_le hkn⟩ : Fin (n + 1)))).toReal
        =
          ENNReal.toReal
            (((PMF.binomial (⟨p, le_of_lt hp.1⟩ : ℝ≥0) (le_of_lt hp.2) n).map
                (fun i : Fin (n + 1) => (i : ℕ))).toMeasure (Set.Ici k)) := by
          -- This is exactly `pmf_fin_tail_eq_nat_tail` specialized to the
          -- binomial PMF on `Fin (n+1)`.
          simpa using
            (pmf_fin_tail_eq_nat_tail (n := n) (k := k) (hkn := hkn)
              (P := PMF.binomial (⟨p, le_of_lt hp.1⟩ : ℝ≥0) (le_of_lt hp.2) n))
      _ = binomial_tail_prob p hp n k := by
          -- Expand `binomial_tail_prob` on the right and identify the two
          -- ℕ-valued PMFs using `fmap_finval_eq_map` and `PMF.map_id`.
          -- Step 1: rewrite the right-hand side.
          simp [binomial_tail_prob]
          -- After the `simp`, the goal is an equality between the tail
          -- probabilities of two PMFs on `ℕ`.
          -- Name these PMFs for clarity.
          set P1 : PMF ℕ :=
            (PMF.binomial (⟨p, le_of_lt hp.1⟩ : ℝ≥0) (le_of_lt hp.2) n).map
              (fun i : Fin (n + 1) => (i : ℕ)) with hP1
          set P2 : PMF ℕ :=
            PMF.map (fun i : ℕ => i)
              (Fin.val <$> PMF.binomial (⟨p, le_of_lt hp.1⟩ : ℝ≥0) (le_of_lt hp.2) n) with hP2
          -- Rewrite the goal using `P1` and `P2`.
          simp [hP1, hP2]
          -- Now the goal is `(P1.toMeasure (Set.Ici k)).toReal =
          -- (P2.toMeasure (Set.Ici k)).toReal`. It suffices to show `P1 = P2`.
          -- First, rewrite `Fin.val <$> binomial` in terms of `P1`.
          have h0 :
              Fin.val <$> PMF.binomial (⟨p, le_of_lt hp.1⟩ : ℝ≥0) (le_of_lt hp.2) n = P1 := by
            -- `fmap_finval_eq_map` gives exactly this, once we simplify with `hP1`.
            simpa [P1, hP1] using
              (fmap_finval_eq_map (n := n)
                (p_nn := (⟨p, le_of_lt hp.1⟩ : ℝ≥0))
                (hp_le := le_of_lt hp.2))
          -- Express `P2` as a `PMF.map` applied to `P1`.
          have h2 :
              P2 = PMF.map (fun i : ℕ => i) P1 := by
            simpa [P2, hP2, h0]
          -- `PMF.map` with the identity function is itself the identity.
          have h_id :
              PMF.map (fun i : ℕ => i) P1 = P1 := by
            simpa [id] using (PMF.map_id (p := P1))
          -- Therefore `P1 = P2`.
          have hmap : P1 = P2 := by
            exact (h2.trans h_id).symm
          -- Transport this equality through `toMeasure` and `toReal` to close the goal.
          simpa using
            congrArg (fun P : PMF ℕ => ((P.toMeasure (Set.Ici k)).toReal)) hmap
    )

open ProbabilityTheory MeasureTheory in
noncomputable def binomial_tail_integral (n k : ℕ) (p : ℝ) : ℝ :=
  (n.choose k : ℝ) * k * ∫ t in (0:ℝ)..p, t^(k-1) * (1-t)^(n-k)

open ProbabilityTheory MeasureTheory in
theorem gaussian_core_fun_mono: MonotoneOn gaussian_core_fun (Set.Icc (1 : ℝ) (4/3 : ℝ)) := by
  classical
  -- Strategy: use the mean value theorem lemma `monotoneOn_of_hasDerivWithinAt_nonneg`
  -- on the convex set I = [1, 4/3].

  have hI_convex : Convex ℝ (Set.Icc (1 : ℝ) (4/3 : ℝ)) := by
    simpa using (convex_Icc (1 : ℝ) (4/3 : ℝ))

  -- Define the derivative function appearing in the lemma.
  let f' : ℝ → ℝ := fun x => 2 * x^(1/2 : ℝ) * Real.exp (1 - x) * ((3/2 : ℝ) - x)

  -- Step 1: continuity of gaussian_core_fun on I.
  have h_cont : ContinuousOn gaussian_core_fun (Set.Icc (1 : ℝ) (4/3 : ℝ)) := by
    -- gaussian_core_fun x = 2 * x^(3/2) * exp (1 - x)
    have h1 : Continuous fun x : ℝ => x^(3/2 : ℝ) := by
      -- exponent 3/2 ≥ 0, so we can use Real.continuous_rpow_const
      have h_exp_nonneg : (0 : ℝ) ≤ (3/2 : ℝ) := by norm_num
      simpa using (Real.continuous_rpow_const h_exp_nonneg)
    have h2 : Continuous fun x : ℝ => Real.exp (1 - x) := by
      refine (Real.continuous_exp.comp ?_)
      exact (continuous_const.sub continuous_id)
    have h_mul : Continuous fun x : ℝ => 2 * x^(3/2 : ℝ) * Real.exp (1 - x) := by
      have : Continuous fun x : ℝ => (2 : ℝ) * x^(3/2 : ℝ) :=
        continuous_const.mul h1
      exact this.mul h2
    -- Restriction of a globally continuous function to I is continuousOn.
    simpa [gaussian_core_fun] using h_mul.continuousOn

  -- Step 2: derivative within the open interval (1,4/3).
  have h_deriv_Ioo :
      ∀ x ∈ Set.Ioo (1 : ℝ) (4/3 : ℝ),
        HasDerivAt gaussian_core_fun (f' x) x := by
    intro x hx
    have hx_pos : 0 < x := lt_trans (by norm_num) hx.1
    -- Use the given derivative formula.
    have h := gaussian_core_fun_deriv x hx_pos
    simpa [f'] using h

  -- On ℝ, the interior of [1,4/3] is (1,4/3).
  have h_interior_Icc :
      interior (Set.Icc (1 : ℝ) (4/3 : ℝ)) = Set.Ioo (1 : ℝ) (4/3 : ℝ) := by
    simpa using interior_Icc (1 : ℝ) (4/3 : ℝ)

  -- Step 3: derivative within the interior of I.
  have h_deriv_within :
      ∀ x ∈ interior (Set.Icc (1 : ℝ) (4/3 : ℝ)),
        HasDerivWithinAt gaussian_core_fun (f' x)
          (interior (Set.Icc (1 : ℝ) (4/3 : ℝ))) x := by
    intro x hx
    -- View x as lying in (1,4/3).
    have hxIoo : x ∈ Set.Ioo (1 : ℝ) (4/3 : ℝ) := by
      simpa [h_interior_Icc] using hx
    -- HasDerivAt on ℝ gives HasDerivWithinAt on any set by `hasDerivAt_hasDerivWithinAt`.
    have h_at : HasDerivAt gaussian_core_fun (f' x) x := h_deriv_Ioo x hxIoo
    exact h_at.hasDerivWithinAt

  -- Step 4: nonnegativity of the derivative on the interior of I.
  have h_deriv_nonneg :
      ∀ x ∈ interior (Set.Icc (1 : ℝ) (4/3 : ℝ)), 0 ≤ f' x := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo (1 : ℝ) (4/3 : ℝ) := by
      simpa [h_interior_Icc] using hx
    -- unpack bounds
    have hx_gt1 : 1 < x := hxIoo.1
    have hx_le_43 : x ≤ (4/3 : ℝ) := hxIoo.2.le
    have hx_pos : 0 < x := lt_trans (by norm_num) hx_gt1
    -- analyze factors in f' x = 2 * x^(1/2) * exp(1-x) * ((3/2) - x)
    have h_two_pos : 0 < (2 : ℝ) := by norm_num
    have h_xpow_nonneg : 0 ≤ x^(1/2 : ℝ) := by
      have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
      exact Real.rpow_nonneg hx_nonneg _
    have h_exp_pos : 0 < Real.exp (1 - x) := Real.exp_pos _
    have h_last_nonneg : 0 ≤ (3/2 : ℝ) - x := by
      have h43_lt_32 : (4/3 : ℝ) < (3/2 : ℝ) := by norm_num
      have hx_lt_32 : x < (3/2 : ℝ) := lt_of_le_of_lt hx_le_43 h43_lt_32
      exact sub_nonneg.mpr (le_of_lt hx_lt_32)
    -- combine: all factors are nonnegative
    have : 0 ≤ (2 : ℝ) * x^(1/2 : ℝ) * Real.exp (1 - x) * ((3/2 : ℝ) - x) := by
      have h_first_nonneg : 0 ≤ (2 : ℝ) * x^(1/2 : ℝ) :=
        mul_nonneg (le_of_lt h_two_pos) h_xpow_nonneg
      have h_first2_nonneg : 0 ≤ (2 : ℝ) * x^(1/2 : ℝ) * Real.exp (1 - x) :=
        mul_nonneg h_first_nonneg (le_of_lt h_exp_pos)
      exact mul_nonneg h_first2_nonneg h_last_nonneg
    simpa [f'] using this

  -- Step 5: apply the monotonicity-from-derivative lemma on a convex set.
  have h_mono : MonotoneOn gaussian_core_fun (Set.Icc (1 : ℝ) (4/3 : ℝ)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Icc (1 : ℝ) (4/3 : ℝ))
      (f := gaussian_core_fun) (f' := f') hI_convex h_cont ?hderiv ?hderiv_nonneg
    · intro x hx
      exact h_deriv_within x hx
    · intro x hx
      exact h_deriv_nonneg x hx
  exact h_mono

open ProbabilityTheory Set in
theorem gaussian_term_deriv (k : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/2)) : let σ := Real.sqrt (p * (1 - p)); let z := (1 / 2 - p) * Real.sqrt (2 * k) / σ; deriv (fun x => 1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) ((1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x)))) p = - ProbabilityTheory.gaussianPDFReal 0 1 z * deriv (fun x => (1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x))) p := by
  dsimp
  let z_fun (x : ℝ) := (1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x))

  -- 1. Differentiability of inner function z_fun at p
  have h_diff_z : DifferentiableAt ℝ z_fun p := by
    unfold z_fun
    apply DifferentiableAt.div
    · apply DifferentiableAt.mul
      · apply DifferentiableAt.sub
        · exact differentiableAt_const _
        · exact differentiableAt_id
      · exact differentiableAt_const _
    · apply DifferentiableAt.sqrt
      · apply DifferentiableAt.mul
        · exact differentiableAt_id
        · apply DifferentiableAt.sub
          · exact differentiableAt_const _
          · exact differentiableAt_id
      · apply ne_of_gt
        nlinarith [hp.1, hp.2]
    · apply Real.sqrt_ne_zero'.mpr
      nlinarith [hp.1, hp.2]

  -- 2. Differentiability of CDF
  let cdf_fun := fun y => cdf (gaussianReal 0 1) y
  have h_diff_cdf (y : ℝ) : DifferentiableAt ℝ cdf_fun y := by
    by_contra h
    have h_deriv_zero : deriv cdf_fun y = 0 := deriv_zero_of_not_differentiableAt h
    rw [gaussian_cdf_deriv] at h_deriv_zero
    have h_pdf_ne_zero : gaussianPDFReal 0 1 y ≠ 0 := by
      rw [gaussianPDFReal]
      dsimp [gaussianPDF]
      apply mul_ne_zero
      · apply inv_ne_zero
        rw [Real.sqrt_ne_zero']
        have : 0 < 2 * π * 1 := by
          have := Real.pi_pos; nlinarith
        exact this
      · apply Real.exp_ne_zero
    contradiction

  -- 3. Calculate derivative
  -- Use chain rule manually step by step
  have h_diff_comp : DifferentiableAt ℝ (cdf_fun ∘ z_fun) p :=
    DifferentiableAt.comp p (h_diff_cdf (z_fun p)) h_diff_z

  -- Use transitivity to match the goal exactly
  apply Eq.trans
  · apply deriv_sub (differentiableAt_const _) h_diff_comp
  · rw [deriv_const]
    rw [zero_sub]
    -- Now simplify the composition
    rw [deriv_comp p (h_diff_cdf (z_fun p)) h_diff_z]
    rw [gaussian_cdf_deriv]
    dsimp [z_fun]
    ring_nf

open ProbabilityTheory Set in
theorem gaussian_tail_tendsto_zero (k : ℕ) (hk : 0 < k) : Filter.Tendsto (fun p : ℝ => 1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p)))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  classical
  -- Goal: as p → 0⁺, the Gaussian tail at
  --   x(p) = ((1/2 - p) * √(2k)) / √(p(1-p))
  -- goes to 0. We show x(p) → +∞ and then use cdf → 1 at +∞.

  -- Shorthand for √2 * √k.
  let C : ℝ := Real.sqrt 2 * Real.sqrt (k : ℝ)

  -- Positivity of k and C.
  have h_k_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hC_pos : 0 < C := by
    have h2_pos : 0 < (2 : ℝ) := by norm_num
    have hsqrt2_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr h2_pos
    have hsqrtk_pos : 0 < Real.sqrt (k : ℝ) :=
      Real.sqrt_pos.mpr h_k_pos
    exact _root_.mul_pos hsqrt2_pos hsqrtk_pos

  -- 1. Limit of p as p → 0⁺ within (0, ∞).
  have h_p : Filter.Tendsto (fun p : ℝ => p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    -- Start with tendsto_id on nhdsWithin and weaken the target filter.
    have h_within :
        Filter.Tendsto (fun p : ℝ => p)
          (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
      Filter.tendsto_id
    exact h_within.mono_right nhdsWithin_le_nhds

  -- 2. Limit of the numerator: (1/2 - p) * C → (1/2) * C.
  have h_num :
      Filter.Tendsto (fun p : ℝ => (1 / 2 - p) * C)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 / 2 : ℝ) * C)) := by
    have h_sub :
        Filter.Tendsto (fun p : ℝ => (1 / 2 : ℝ) - p)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 / 2 : ℝ) - 0)) := by
      have h_const :
          Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) :=
        tendsto_const_nhds
      have h_sub' := Filter.Tendsto.sub h_const h_p
      simpa using h_sub'
    have h_mul := Filter.Tendsto.mul_const C h_sub
    simpa using h_mul

  -- 3. Limit of the inner denominator p*(1-p) → 0.
  have h_den_inner :
      Filter.Tendsto (fun p : ℝ => p * (1 - p))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    -- product of p and (1-p)
    have h_one_minus_p :
        Filter.Tendsto (fun p : ℝ => 1 - p)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 - 0)) :=
      Filter.Tendsto.sub tendsto_const_nhds h_p
    have h_mul := Filter.Tendsto.mul h_p h_one_minus_p
    simpa using h_mul

  -- 4. Use the general lemma `Filter.Tendsto.sqrt` to get the limit of the square root.
  have h_den_sqrt :
      Filter.Tendsto (fun p : ℝ => Real.sqrt (p * (1 - p)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 0)) :=
    Filter.Tendsto.sqrt h_den_inner
  have h_den_sqrt' :
      Filter.Tendsto (fun p : ℝ => Real.sqrt (p * (1 - p)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using h_den_sqrt

  -- 5. Show that sqrt(p*(1-p)) stays positive eventually, using `sigma_pos`.
  have h_den_pos :
      Filter.Eventually (fun p : ℝ => 0 < Real.sqrt (p * (1 - p)))
        (nhdsWithin 0 (Set.Ioi 0)) := by
    -- On the right neighborhood of 0, we can restrict to p ∈ (0,1/2).
    have hIoo : Set.Ioo (0 : ℝ) (1 / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      -- Use the characterization by an auxiliary neighborhood in ℝ.
      refine (mem_nhdsWithin_iff_exists_mem_nhds_inter).2 ?_
      -- Take U = (-1/4, 1/2).
      refine ⟨Set.Ioo (-(1 / 4 : ℝ)) (1 / 2), ?_, ?_⟩
      · -- U is a neighborhood of 0 in ℝ.
        have hleft : -(1 / 4 : ℝ) < (0 : ℝ) := by norm_num
        have hright : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
        simpa using (Ioo_mem_nhds hleft hright)
      · -- U ∩ (0,∞) ⊆ (0,1/2).
        intro x hx
        rcases hx with ⟨hxU, hx_pos⟩
        rcases hxU with ⟨hx_gt_neg, hx_lt_half⟩
        exact ⟨hx_pos, hx_lt_half⟩
    -- Turn this membership into an eventual statement on the filter.
    have h_eventually :
        Filter.Eventually (fun p : ℝ => p ∈ Set.Ioo (0 : ℝ) (1 / 2))
          (nhdsWithin 0 (Set.Ioi 0)) :=
      hIoo
    -- Apply sigma_pos on that eventual membership.
    refine h_eventually.mono ?_
    intro p hp
    have hpos := sigma_pos p hp
    simpa using hpos

  -- 6. Upgrade the limit of sqrt to a limit within the positive side, so that
  -- we can compose with inversion.
  have h_den_t_within :
      Filter.Tendsto (fun p : ℝ => Real.sqrt (p * (1 - p)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      _ h_den_sqrt' h_den_pos

  -- 7. Limit of the inverse: (sqrt(p*(1-p)))⁻¹ → +∞ as p → 0⁺.
  have h_inv :
      Filter.Tendsto (fun p : ℝ => (Real.sqrt (p * (1 - p)))⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    have h_inv_core :
        Filter.Tendsto (fun x : ℝ => x⁻¹)
          (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
      tendsto_inv_nhdsGT_zero
    exact Filter.Tendsto.comp h_inv_core h_den_t_within

  -- 8. The limit of the constant multiple (1/2)*C is positive.
  have h_num_pos_lim : 0 < (1 / 2 : ℝ) * C := by
    have : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    exact _root_.mul_pos this hC_pos

  -- 9. The argument of the CDF tends to +∞.
  have h_arg :
      Filter.Tendsto
        (fun p : ℝ => ((1 / 2 - p) * C) / Real.sqrt (p * (1 - p)))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simp only [div_eq_mul_inv]
    have h_mul := Filter.Tendsto.pos_mul_atTop h_num_pos_lim h_num h_inv
    simpa using h_mul

  -- 10. The Gaussian CDF tends to 1 at +∞.
  have h_cdf :
      Filter.Tendsto (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1))
        Filter.atTop (nhds (1 : ℝ)) :=
    ProbabilityTheory.tendsto_cdf_atTop (ProbabilityTheory.gaussianReal 0 1)

  -- 11. Compose: CDF of the argument tends to 1.
  have h_comp :
      Filter.Tendsto
        (fun p : ℝ =>
          ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
            (((1 / 2 - p) * C) / Real.sqrt (p * (1 - p))))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ)) :=
    h_cdf.comp h_arg

  -- 12. Finally, `1 - cdf(argument)` tends to 0.
  have h_final :
      Filter.Tendsto
        (fun p : ℝ =>
          1 -
            ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
              (((1 / 2 - p) * C) / Real.sqrt (p * (1 - p))))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 - (1 : ℝ))) := by
    have h_const :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ)) :=
      tendsto_const_nhds
    have h_sub := Filter.Tendsto.sub h_const h_comp
    simpa using h_sub

  -- 13. Rewriting the limit value as 0 and unfolding C in the expression.
  have h_zero : (1 - (1 : ℝ)) = (0 : ℝ) := by norm_num
  -- Now rewrite C in terms of the original √(2 * k).
  have hC_def : C = Real.sqrt 2 * Real.sqrt (k : ℝ) := rfl
  simpa [h_zero, hC_def, C] using h_final

open Filter Topology ProbabilityTheory in
theorem limit_gaussian_tail_bound_region2: Filter.Tendsto (fun z => (1 - z / Real.sqrt (z^2 + 1)) - 2 * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (z * Real.sqrt 2))) Filter.atTop (nhds 0) := by
  -- We show each component tends to its limit and then combine.
  have h1 : Tendsto (fun z : ℝ => z / Real.sqrt (z ^ 2 + 1)) atTop (nhds (1 : ℝ)) := by
    -- For large positive z, rewrite using the provided identity.
    have h_eq : (fun z : ℝ => z / Real.sqrt (z ^ 2 + 1)) =ᶠ[atTop]
        (fun z => 1 / Real.sqrt (1 + (z⁻¹) ^ 2)) := by
      filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ)] with z hz
      exact div_sqrt_identity z hz
    -- Now compute the limit of the right-hand side and transfer it back.
    refine Filter.Tendsto.congr' h_eq.symm ?_
    -- Limit of 1 / sqrt(1 + (z⁻¹)^2) as z → ∞.
    have lim_inv : Tendsto (fun z : ℝ => z⁻¹) atTop (nhds (0 : ℝ)) := tendsto_inv_atTop_zero
    have lim_sq : Tendsto (fun z : ℝ => (z⁻¹) ^ 2) atTop (nhds (0 : ℝ)) := by
      simpa using lim_inv.pow 2
    have lim_inner : Tendsto (fun z : ℝ => 1 + (z⁻¹) ^ 2) atTop (nhds (1 : ℝ)) := by
      simpa using lim_sq.const_add 1
    have lim_sqrt : Tendsto (fun z : ℝ => Real.sqrt (1 + (z⁻¹) ^ 2)) atTop (nhds (1 : ℝ)) := by
      simpa using lim_inner.sqrt
    -- Use Tendsto.inv₀ to get the limit of the reciprocal.
    have h_ne : (1 : ℝ) ≠ 0 := one_ne_zero
    have h_inv :
        Tendsto (fun z : ℝ => (Real.sqrt (1 + (z⁻¹) ^ 2))⁻¹) atTop (nhds ((1 : ℝ)⁻¹)) :=
      Filter.Tendsto.inv₀ lim_sqrt h_ne
    -- Since 1⁻¹ = 1 and (·)⁻¹ = 1 / ·, this is our desired limit.
    simpa [one_div] using h_inv

  have h2 :
      Tendsto (fun z : ℝ => 2 * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (z * Real.sqrt 2)))
        atTop (nhds (0 : ℝ)) := by
    -- First, the inner argument z * sqrt 2 tends to +∞.
    have hpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have h_arg : Tendsto (fun z : ℝ => z * Real.sqrt 2) atTop atTop :=
      Filter.Tendsto.atTop_mul_const' hpos tendsto_id
    -- The Gaussian cdf tends to 1 at +∞.
    have h_cdf := ProbabilityTheory.tendsto_cdf_atTop (ProbabilityTheory.gaussianReal 0 1)
    have h_comp :
        Tendsto (fun z : ℝ => ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (z * Real.sqrt 2))
          atTop (nhds (1 : ℝ)) := by
      simpa [Function.comp] using h_cdf.comp h_arg
    -- Therefore 1 - cdf(...) tends to 0.
    have h_sub' :
        Tendsto (fun z : ℝ => (1 : ℝ) - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (z * Real.sqrt 2))
          atTop (nhds ((1 : ℝ) - 1)) :=
      tendsto_const_nhds.sub h_comp
    have h_sub :
        Tendsto (fun z : ℝ => (1 : ℝ) - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (z * Real.sqrt 2))
          atTop (nhds (0 : ℝ)) := by
      simpa using h_sub'
    -- Multiply by 2, preserving the limit 0.
    have h_mul' :
        Tendsto (fun z : ℝ => (2 : ℝ) * ((1 : ℝ) - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (z * Real.sqrt 2)))
          atTop (nhds ((2 : ℝ) * 0)) :=
      tendsto_const_nhds.mul h_sub
    have h_mul :
        Tendsto (fun z : ℝ => 2 * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (z * Real.sqrt 2)))
          atTop (nhds (0 : ℝ)) := by
      simpa [sub_eq_add_neg] using h_mul'
    exact h_mul

  -- Now combine the limits: 1 - z/sqrt(z^2+1) → 0 and 2*(1 - cdf(...)) → 0,
  -- so their difference also tends to 0.
  have h_main' :
      Tendsto (fun z : ℝ => (1 : ℝ) - z / Real.sqrt (z ^ 2 + 1)) atTop (nhds ((1 : ℝ) - 1)) :=
    tendsto_const_nhds.sub h1
  have h_main :
      Tendsto (fun z : ℝ => (1 : ℝ) - z / Real.sqrt (z ^ 2 + 1)) atTop (nhds (0 : ℝ)) := by
    simpa using h_main'

  have h_total :
      Tendsto
        (fun z : ℝ => (1 : ℝ) - z / Real.sqrt (z ^ 2 + 1)
          - 2 * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (z * Real.sqrt 2)))
        atTop (nhds (0 - 0 : ℝ)) :=
    h_main.sub h2
  simpa [sub_eq_add_neg] using h_total

open Filter Topology in
theorem R_aux_limit_atTop: Tendsto R_aux atTop (nhds 0) := by
  let f := fun (z : ℝ) => z^3 * Real.exp (-z^2)
  let g := fun (z : ℝ) => (1 + z⁻¹ ^ 2) ^ (3/2 : ℝ)
  let c := 2 / Real.sqrt Real.pi

  have h_eq : R_aux =ᶠ[atTop] fun z => c * (f z * g z) := by
    filter_upwards [Filter.Ioi_mem_atTop 0] with z hz
    dsimp [R_aux, f, g, c]
    rw [mul_comm (z^3), mul_assoc (Real.exp _), mul_assoc c]
    congr 1
    congr 1

    have h_z : 0 ≤ z := le_of_lt hz
    have h_z2 : 0 ≤ z^2 := sq_nonneg z
    have h_z2_pos : 0 < z^2 := pow_pos hz 2
    have h_inv : 0 ≤ 1 + z⁻¹ ^ 2 := add_nonneg zero_le_one (sq_nonneg _)
    have h_zne : z ≠ 0 := ne_of_gt hz

    have h_pow_eq : z^3 = (z^2) ^ (3/2 : ℝ) := by
      rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num]
      rw [Real.rpow_add h_z2_pos]
      rw [Real.rpow_one]
      rw [← Real.sqrt_eq_rpow]
      rw [Real.sqrt_sq h_z]
      ring

    rw [h_pow_eq]
    rw [← Real.mul_rpow h_z2 h_inv]
    congr 1
    field_simp [h_zne]

  apply Tendsto.congr' h_eq.symm

  have h_lim_f : Tendsto f atTop (nhds 0) := by
    have := gaussian_limit_zero_helper_sq 3 1 (by norm_num)
    convert this using 1
    funext z
    simp [f]

  have h_lim_g : Tendsto g atTop (nhds 1) := by
    have h1 : Tendsto (fun (z : ℝ) => z⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have h2 : Tendsto (fun (z : ℝ) => 1 + z⁻¹ ^ 2) atTop (nhds (1 + 0^2)) := by
      apply Tendsto.add tendsto_const_nhds
      apply Tendsto.pow h1 2
    rw [zero_pow two_ne_zero, add_zero] at h2

    have h3 : ContinuousAt (fun x : ℝ => x ^ (3/2 : ℝ)) 1 := by
      apply Real.continuousAt_rpow_const
      exact Or.inl (ne_of_gt zero_lt_one)

    convert (Tendsto.comp h3.tendsto h2) using 1
    simp

  rw [show (0:ℝ) = c * (0 * 1) by ring]
  exact Tendsto.const_mul c (Tendsto.mul h_lim_f h_lim_g)

open Filter Topology in
theorem BA_lower_from_central (k : ℕ) (hk : 0 < k) :
  let A := (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * k
  let B := Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi)
  1 / (2 * (4 : ℝ) ^ k) ≤ B / A := by
  classical
  -- We first rewrite the square root in the central binomial bound
  have hπ_nonneg : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have hk_nonneg : 0 ≤ (k : ℝ) := by
    exact_mod_cast (Nat.zero_le k)
  have hsqrt_mul : Real.sqrt (Real.pi * k) = Real.sqrt Real.pi * Real.sqrt (k : ℝ) := by
    -- This is sqrt (π * k) = sqrt π * sqrt k, using nonnegativity
    simpa using (Real.sqrt_mul hπ_nonneg hk_nonneg)

  -- Apply the given central binomial coefficient bound and rewrite the denominator
  have h0' : ((2 * k).choose k : ℝ) ≤ (4 : ℝ) ^ k / (Real.sqrt Real.pi * Real.sqrt (k : ℝ)) := by
    simpa [hsqrt_mul] using (central_binom_bound_sqrt k hk)

  -- The factor we will multiply by is positive
  have hM_pos : 0 < Real.sqrt Real.pi * Real.sqrt (k : ℝ) := by
    have h1 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hk_pos' : 0 < (k : ℝ) := by
      exact_mod_cast hk
    have h2 : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk_pos'
    exact _root_.mul_pos h1 h2

  -- Multiply the inequality by this positive factor
  have h1 : ((2 * k).choose k : ℝ) * (Real.sqrt Real.pi * Real.sqrt (k : ℝ)) ≤ (4 : ℝ) ^ k := by
    have := (le_div_iff₀ hM_pos).1 h0'
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

  -- Now multiply both sides by 2 ≥ 0
  have h1' : 2 * ((2 * k).choose k : ℝ) * Real.sqrt Real.pi * Real.sqrt (k : ℝ) ≤ 2 * (4 : ℝ) ^ k := by
    have htemp := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 by norm_num)
    simpa [mul_comm, mul_left_comm, mul_assoc] using htemp

  -- Show positivity of the denominator on the right-hand side
  have hCpos_nat : 0 < (2 * k).choose k := by
    -- since k ≤ 2k, the binomial coefficient is positive
    have hk_le_kk : k ≤ k + k := Nat.le_add_left k k
    have hk_le_2k : k ≤ 2 * k := by
      simpa [two_mul] using hk_le_kk
    exact Nat.choose_pos hk_le_2k
  have hCpos : 0 < ((2 * k).choose k : ℝ) := by
    exact_mod_cast hCpos_nat
  have hsqrtπ_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsqrtk_pos : 0 < Real.sqrt (k : ℝ) := by
    have hk_pos' : 0 < (k : ℝ) := by
      exact_mod_cast hk
    exact Real.sqrt_pos.mpr hk_pos'
  have hdenom_pos : 0 < 2 * ((2 * k).choose k : ℝ) * Real.sqrt Real.pi * Real.sqrt (k : ℝ) := by
    have hpos1 : 0 < ((2 * k).choose k : ℝ) * Real.sqrt Real.pi := mul_pos hCpos hsqrtπ_pos
    have hpos2 : 0 < ((2 * k).choose k : ℝ) * Real.sqrt Real.pi * Real.sqrt (k : ℝ) :=
      mul_pos hpos1 hsqrtk_pos
    have h2 : 0 < (2 : ℝ) := by norm_num
    have htemp : 0 < (2 : ℝ) * (((2 * k).choose k : ℝ) * Real.sqrt Real.pi * Real.sqrt (k : ℝ)) :=
      mul_pos h2 hpos2
    simpa [mul_comm, mul_left_comm, mul_assoc] using htemp

  -- Apply the monotonicity of reciprocal on positive reals
  have hfinal :
      1 / (2 * (4 : ℝ) ^ k) ≤
        1 / (2 * ((2 * k).choose k : ℝ) * Real.sqrt Real.pi * Real.sqrt (k : ℝ)) := by
    exact one_div_le_one_div_of_le hdenom_pos h1'

  -- Use the closed form for B / A to conclude
  simpa [(BA_closed_form k hk).symm] using hfinal

open Finset in
theorem central_tail_sum_even_int (k : ℕ) (hk : 0 < k) : ∑ i ∈ Finset.Icc k (2 * k), (Nat.choose (2 * k) i : ℝ) = (2 : ℝ) ^ (2 * k - 1) + (Nat.choose (2 * k) k : ℝ) / 2 := by
  let n := 2 * k
  have hn : n = 2 * k := rfl
  have hn_pos : 0 < n := by omega

  let L := ∑ i ∈ Finset.Icc 0 (k - 1), (Nat.choose n i : ℝ)
  let C := (Nat.choose n k : ℝ)
  let U := ∑ i ∈ Finset.Icc (k + 1) n, (Nat.choose n i : ℝ)

  have h_tails : L = U := choose_even_tails_equal_real k hk

  have h_split : ∑ i ∈ Finset.Icc 0 n, (Nat.choose n i : ℝ) = L + C + U :=
    sum_choose_split_at_middle_real k hk

  have h_range : Finset.range (n + 1) = Finset.Icc 0 n := by
    ext i
    simp [mem_Icc, mem_range]
    omega

  have h_total : ∑ i ∈ Finset.Icc 0 n, (Nat.choose n i : ℝ) = (2 : ℝ) ^ n := by
    rw [← h_range]
    rw [← Nat.cast_sum]
    rw [Nat.sum_range_choose]
    simp

  have h_sum_eq : L + C + U = (2 : ℝ) ^ n := by
    rw [← h_split]
    exact h_total

  have h_alg : C + U = (2 : ℝ) ^ (n - 1) + C / 2 :=
    central_tail_algebra n hn_pos L C U h_tails h_sum_eq

  -- Transform the goal to match h_alg
  rw [← hn]

  have h_decomp : Finset.Icc k n = {k} ∪ Finset.Icc (k + 1) n := by
    ext x
    simp [mem_Icc, mem_singleton, mem_union]
    constructor <;> intro h <;> omega

  have h_disj : Disjoint {k} (Finset.Icc (k + 1) n) := by
    rw [disjoint_singleton_left, mem_Icc]
    omega

  rw [h_decomp, sum_union h_disj, sum_singleton]

  change C + U = (2 : ℝ) ^ (n - 1) + C / 2

  exact h_alg

open Set in
theorem L_aux_shape: StrictMonoOn L_aux (Icc 0 (1 / Real.sqrt 2)) ∧ StrictAntiOn L_aux (Ici (1 / Real.sqrt 2)) := by
  classical
  -- convenient name for the derivative formula
  have h_deriv : ∀ z, deriv L_aux z = z * (1 - 2 * z ^ 2) / (z ^ 2 + 1) :=
    L_aux_deriv_calc
  constructor
  · -- Strictly increasing on [0, 1/√2]
    -- basic building blocks for continuity
    have hsq_global : Continuous fun z : ℝ => z ^ 2 := by
      simpa using (continuous_id'.pow 2 : Continuous fun z : ℝ => z ^ 2)
    have hlog_arg_global : Continuous fun z : ℝ => z ^ 2 + 1 :=
      hsq_global.add continuous_const
    -- continuity of log on ℝ \ {0}
    have hlog_on : ContinuousOn Real.log ({0} : Set ℝ)ᶜ :=
      Real.continuousOn_log
    -- continuity of L_aux on [0, 1/√2]
    have hcont1 : ContinuousOn L_aux (Icc 0 (1 / Real.sqrt 2)) := by
      -- continuity of z ↦ z^2 on the interval
      have hsq1 : ContinuousOn (fun z : ℝ => z ^ 2) (Icc 0 (1 / Real.sqrt 2)) :=
        hsq_global.continuousOn
      -- continuity of z ↦ z^2 + 1 on the interval
      have hlog_arg1 : ContinuousOn (fun z : ℝ => z ^ 2 + 1) (Icc 0 (1 / Real.sqrt 2)) :=
        hlog_arg_global.continuousOn
      -- its image avoids 0, so we can compose with log
      have hmaps1 : MapsTo (fun z : ℝ => z ^ 2 + 1)
          (Icc 0 (1 / Real.sqrt 2)) ({0} : Set ℝ)ᶜ := by
        intro x hx
        have hxpos : 0 < x ^ 2 + 1 := by
          have hx2 : (0 : ℝ) ≤ x ^ 2 := by
            have := sq_nonneg x
            simpa using this
          exact add_pos_of_nonneg_of_pos hx2 (by norm_num)
        have hxne : (x ^ 2 + 1 : ℝ) ≠ 0 := ne_of_gt hxpos
        classical
        simpa using hxne
      -- continuity of z ↦ log (z^2+1) on the interval
      have hlog1 : ContinuousOn (fun z : ℝ => Real.log (z ^ 2 + 1))
          (Icc 0 (1 / Real.sqrt 2)) := by
        -- compose log with z^2+1, using continuity on {0}ᶜ and that image avoids 0
        have h := hlog_on.comp hlog_arg1 hmaps1
        simpa [Function.comp] using h
      -- constant term is continuous on the interval
      have hconst1 : ContinuousOn (fun _ : ℝ => Real.log (2 / Real.sqrt Real.pi))
          (Icc 0 (1 / Real.sqrt 2)) :=
        continuousOn_const
      -- assemble L_aux from its pieces
      unfold L_aux
      -- L_aux z = const - z^2 + (3/2) * log (z^2 + 1)
      have h1 : ContinuousOn (fun z : ℝ =>
          Real.log (2 / Real.sqrt Real.pi) - z ^ 2)
          (Icc 0 (1 / Real.sqrt 2)) :=
        hconst1.sub hsq1
      have h2 : ContinuousOn (fun z : ℝ =>
          (3 / 2 : ℝ) * Real.log (z ^ 2 + 1))
          (Icc 0 (1 / Real.sqrt 2)) := by
        have hconst_mul : ContinuousOn (fun _ : ℝ => (3 / 2 : ℝ))
            (Icc 0 (1 / Real.sqrt 2)) := continuousOn_const
        exact hconst_mul.mul hlog1
      -- sum of continuous functions is continuous
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc]
        using h1.add h2
    -- convexity of the interval
    have hconv1 : Convex ℝ (Icc 0 (1 / Real.sqrt 2)) := by
      simpa using (convex_Icc (0 : ℝ) (1 / Real.sqrt 2))
    -- use derivative sign on the interior
    refine strictMonoOn_of_deriv_pos hconv1 hcont1 ?hderiv_pos
    intro x hx
    -- x is in the interior of [0, 1/√2], i.e. in (0, 1/√2)
    have hx' : x ∈ Ioo (0 : ℝ) (1 / Real.sqrt 2) := by
      simpa [interior_Icc] using hx
    rcases hx' with ⟨hx0, hx1⟩
    -- derivative formula
    have hder : deriv L_aux x = x * (1 - 2 * x ^ 2) / (x ^ 2 + 1) :=
      h_deriv x
    -- denominator positive
    have hden : 0 < x ^ 2 + 1 := by
      have hx2 : (0 : ℝ) ≤ x ^ 2 := by
        have := sq_nonneg x
        simpa using this
      exact add_pos_of_nonneg_of_pos hx2 (by norm_num)
    -- sign of numerator: x > 0 and 1 - 2 x^2 > 0
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hx0_pos : 0 < x := hx0
    -- from x < 1/√2 infer √2 * x < 1
    have hx_mul : Real.sqrt 2 * x < 1 := by
      have hx_mul' : Real.sqrt 2 * x < Real.sqrt 2 * (1 / Real.sqrt 2) :=
        (mul_lt_mul_of_pos_left hx1 hsqrt2_pos)
      have hsqrt_ne : (Real.sqrt 2 : ℝ) ≠ 0 := ne_of_gt hsqrt2_pos
      have : Real.sqrt 2 * (1 / Real.sqrt 2) = (1 : ℝ) := by
        field_simp [one_div, hsqrt_ne]
      simpa [this] using hx_mul'
    -- square both sides using sq_lt_sq₀ (since both sides are nonnegative)
    have hx_mul_nonneg : 0 ≤ Real.sqrt 2 * x :=
      mul_nonneg (le_of_lt hsqrt2_pos) (le_of_lt hx0_pos)
    have hone_nonneg : 0 ≤ (1 : ℝ) := by norm_num
    have hx_mul_sq : (Real.sqrt 2 * x) ^ 2 < (1 : ℝ) ^ 2 := by
      have := (sq_lt_sq₀ hx_mul_nonneg hone_nonneg).2 hx_mul
      simpa [pow_two] using this
    -- rewrite squares: (√2 * x)^2 = 2 * x^2 and 1^2 = 1
    have h_sqrt_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
      have hpos2 : (0 : ℝ) ≤ 2 := by norm_num
      simpa [pow_two] using (Real.sq_sqrt hpos2)
    have h2xsq_lt_one : 2 * x ^ 2 < 1 := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, h_sqrt_sq] using
        hx_mul_sq
    -- hence 1 - 2 x^2 > 0
    have hnum1 : 0 < 1 - 2 * x ^ 2 :=
      sub_pos.mpr h2xsq_lt_one
    have hnum : 0 < x * (1 - 2 * x ^ 2) :=
      mul_pos hx0_pos hnum1
    -- combine sign of numerator and denominator
    have : 0 < x * (1 - 2 * x ^ 2) / (x ^ 2 + 1) :=
      div_pos hnum hden
    -- conclude for derivative
    simpa [hder] using this
  · -- Strictly decreasing on [1/√2, ∞)
    -- same continuity ingredients as before
    have hsq_global : Continuous fun z : ℝ => z ^ 2 := by
      simpa using (continuous_id'.pow 2 : Continuous fun z : ℝ => z ^ 2)
    have hlog_arg_global : Continuous fun z : ℝ => z ^ 2 + 1 :=
      hsq_global.add continuous_const
    have hlog_on : ContinuousOn Real.log ({0} : Set ℝ)ᶜ :=
      Real.continuousOn_log
    -- continuity of L_aux on [1/√2, ∞)
    have hcont2 : ContinuousOn L_aux (Ici (1 / Real.sqrt 2)) := by
      have hsq2 : ContinuousOn (fun z : ℝ => z ^ 2) (Ici (1 / Real.sqrt 2)) :=
        hsq_global.continuousOn
      have hlog_arg2 : ContinuousOn (fun z : ℝ => z ^ 2 + 1) (Ici (1 / Real.sqrt 2)) :=
        hlog_arg_global.continuousOn
      have hmaps2 : MapsTo (fun z : ℝ => z ^ 2 + 1)
          (Ici (1 / Real.sqrt 2)) ({0} : Set ℝ)ᶜ := by
        intro x hx
        have hxpos : 0 < x ^ 2 + 1 := by
          have hx2 : (0 : ℝ) ≤ x ^ 2 := by
            have := sq_nonneg x
            simpa using this
          exact add_pos_of_nonneg_of_pos hx2 (by norm_num)
        have hxne : (x ^ 2 + 1 : ℝ) ≠ 0 := ne_of_gt hxpos
        classical
        simpa using hxne
      have hlog2 : ContinuousOn (fun z : ℝ => Real.log (z ^ 2 + 1))
          (Ici (1 / Real.sqrt 2)) := by
        have h := hlog_on.comp hlog_arg2 hmaps2
        simpa [Function.comp] using h
      have hconst2 : ContinuousOn (fun _ : ℝ => Real.log (2 / Real.sqrt Real.pi))
          (Ici (1 / Real.sqrt 2)) :=
        continuousOn_const
      unfold L_aux
      have h1 : ContinuousOn (fun z : ℝ =>
          Real.log (2 / Real.sqrt Real.pi) - z ^ 2)
          (Ici (1 / Real.sqrt 2)) :=
        hconst2.sub hsq2
      have h2 : ContinuousOn (fun z : ℝ =>
          (3 / 2 : ℝ) * Real.log (z ^ 2 + 1))
          (Ici (1 / Real.sqrt 2)) := by
        have hconst_mul : ContinuousOn (fun _ : ℝ => (3 / 2 : ℝ))
            (Ici (1 / Real.sqrt 2)) := continuousOn_const
        exact hconst_mul.mul hlog2
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc]
        using h1.add h2
    have hconv2 : Convex ℝ (Ici (1 / Real.sqrt 2)) := by
      simpa using (convex_Ici (1 / Real.sqrt 2 : ℝ))
    refine strictAntiOn_of_deriv_neg hconv2 hcont2 ?hderiv_neg
    intro x hx
    -- x is in the interior of [1/√2, ∞), i.e. in (1/√2, ∞)
    have hx' : x ∈ Ioi (1 / Real.sqrt 2) := by
      simpa [interior_Ici] using hx
    have hx1 : 1 / Real.sqrt 2 < x := hx'
    -- 1/√2 > 0, hence x > 0
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hhalf_pos : 0 < (1 / Real.sqrt 2 : ℝ) :=
      one_div_pos.mpr hsqrt2_pos
    have hx0 : 0 < x := lt_trans hhalf_pos hx1
    -- denominator positive
    have hden : 0 < x ^ 2 + 1 := by
      have hx2 : (0 : ℝ) ≤ x ^ 2 := by
        have := sq_nonneg x
        simpa using this
      exact add_pos_of_nonneg_of_pos hx2 (by norm_num)
    -- derivative formula
    have hder : deriv L_aux x = x * (1 - 2 * x ^ 2) / (x ^ 2 + 1) :=
      h_deriv x
    -- sign of numerator: x > 0 and 1 - 2x^2 < 0
    -- from 1/√2 < x infer 1 < √2 * x
    have hx_mul : (1 : ℝ) < Real.sqrt 2 * x := by
      have hx_mul' : Real.sqrt 2 * (1 / Real.sqrt 2) < Real.sqrt 2 * x :=
        (mul_lt_mul_of_pos_left hx1 hsqrt2_pos)
      have hsqrt_ne : (Real.sqrt 2 : ℝ) ≠ 0 := ne_of_gt hsqrt2_pos
      have : Real.sqrt 2 * (1 / Real.sqrt 2) = (1 : ℝ) := by
        field_simp [one_div, hsqrt_ne]
      simpa [this] using hx_mul'
    -- square both sides to get 1 < 2 x^2
    have hx_mul_nonneg : 0 ≤ Real.sqrt 2 * x :=
      mul_nonneg (le_of_lt hsqrt2_pos) (le_of_lt hx0)
    have hone_nonneg : 0 ≤ (1 : ℝ) := by norm_num
    have hx_mul_sq : (1 : ℝ) ^ 2 < (Real.sqrt 2 * x) ^ 2 := by
      have := (sq_lt_sq₀ hone_nonneg hx_mul_nonneg).2 hx_mul
      simpa [pow_two] using this
    have h_sqrt_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
      have hpos2 : (0 : ℝ) ≤ 2 := by norm_num
      simpa [pow_two] using (Real.sq_sqrt hpos2)
    have h_one_lt_2xsq : 1 < 2 * x ^ 2 := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, h_sqrt_sq] using
        hx_mul_sq
    -- hence 1 - 2 x^2 < 0
    have hnum1 : 1 - 2 * x ^ 2 < 0 :=
      sub_lt_zero.mpr h_one_lt_2xsq
    have hnum : x * (1 - 2 * x ^ 2) < 0 := by
      -- product of positive and negative
      exact mul_neg_of_pos_of_neg hx0 hnum1
    -- combine numerator and denominator
    have : x * (1 - 2 * x ^ 2) / (x ^ 2 + 1) < 0 :=
      div_neg_of_neg_of_pos hnum hden
    have : deriv L_aux x < 0 := by
      simpa [hder] using this
    exact this

open NNReal ENNReal Set in
theorem binomial_mass_at_k_two_k (p : NNReal) (hp : p ≤ 1) (k : ℕ) : (((PMF.binomial p hp (2 * k)).map (λ i => (i : ℕ))) k).toReal = ((Nat.choose (2 * k) k) : ℝ) * (p : ℝ) ^ k * ((1 : ℝ) - p) ^ k := by
  let n := 2 * k
  have h_n_def : n = 2 * k := rfl
  have h_le : k ≤ n := by
    rw [h_n_def, Nat.two_mul]
    exact Nat.le_add_right k k
  have h_sub : n - k = k := by
    rw [h_n_def, Nat.two_mul]
    exact Nat.add_sub_cancel_left k k
  rw [pmf_binomial_apply_coe_le p hp n k h_le]
  rw [h_sub]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  congr
  rw [ENNReal.toReal_sub_of_le]
  · simp
  · simp
    exact hp
  · simp

open NNReal ENNReal ProbabilityTheory Set in
theorem differentiable_cdf_gaussianReal: Differentiable ℝ (cdf (gaussianReal 0 1)) := by
  intro x
  exact (gaussian_cdf_hasDerivAt_lemma x).differentiableAt

open NNReal ENNReal ProbabilityTheory Set in
theorem gaussian_tail_bound_derivative_strategy (p : ℝ) (hp : p ∈ Set.Ioo 0 (1 / 2)) : DifferentiableAt ℝ (fun x => cdf (gaussianReal 0 1) ((1 / 2 - x) * Real.sqrt 2 / Real.sqrt (x * (1 - x)))) p := by
  let z := fun x => (1 / 2 - x) * Real.sqrt 2 / Real.sqrt (x * (1 - x))
  have h_outer : DifferentiableAt ℝ (fun y => cdf (gaussianReal 0 1) y) (z p) :=
    (gaussian_cdf_hasDerivAt_lemma (z p)).differentiableAt
  have h_inner : DifferentiableAt ℝ z p := by
    dsimp [z]
    apply DifferentiableAt.div
    · apply DifferentiableAt.mul
      · apply DifferentiableAt.sub
        · exact differentiableAt_const (1/2)
        · exact differentiableAt_id
      · exact differentiableAt_const (Real.sqrt 2)
    · apply DifferentiableAt.sqrt
      · apply DifferentiableAt.mul
        · exact differentiableAt_id
        · apply DifferentiableAt.sub
          · exact differentiableAt_const 1
          · exact differentiableAt_id
      · have h_pos := sigma_pos p hp
        rw [Real.sqrt_pos] at h_pos
        exact h_pos.ne'
    · exact (sigma_pos p hp).ne'
  apply DifferentiableAt.comp
  · exact h_outer
  · exact h_inner

open NNReal ENNReal ProbabilityTheory Set in
theorem gaussian_calculus_helpers (x : ℝ) : deriv (fun x => ProbabilityTheory.cdf (gaussianReal 0 1) x) x = ProbabilityTheory.gaussianPDFReal 0 1 x ∧ ProbabilityTheory.cdf (gaussianReal 0 1) 0 = 1/2 := by
  constructor
  · exact (gaussian_cdf_hasDerivAt_lemma x).deriv
  · exact gaussian_cdf_zero_eq_half

open NNReal ENNReal ProbabilityTheory Set in
theorem hasDerivAt_gaussian_cdf_scaled (x : ℝ) : HasDerivAt (fun t : ℝ => ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (t * Real.sqrt 2)) (ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2) * Real.sqrt 2) x := by
  -- Use chain rule on F ∘ h where
  -- F y = cdf (gaussianReal 0 1) y and h t = t * Real.sqrt 2
  have hF : HasDerivAt (fun y => cdf (gaussianReal 0 1) y) (gaussianPDFReal 0 1 (x * Real.sqrt 2)) (x * Real.sqrt 2) := by
    -- instantiate the lemma at (x * √2)
    simpa using gaussian_cdf_hasDerivAt_lemma (x * Real.sqrt 2)
  -- derivative of h(t) = t * √2 is √2 at x
  have hh : HasDerivAt (fun t : ℝ => t * Real.sqrt 2) (Real.sqrt 2) x := by
    -- use general lemma for derivative of linear function t ↦ t * c
    have hId : HasDerivAt (fun t : ℝ => t) (1 : ℝ) x := by
      -- derivative of identity is 1
      simpa using (hasDerivAt_id (x := x))
    -- multiply by constant √2 on the right
    simpa [one_mul] using hId.mul_const (Real.sqrt 2)
  -- apply chain rule: outer derivative hF, inner derivative hh
  have hcomp := hF.comp x hh
  -- hcomp already has the right form for our statement
  simpa using hcomp

open NNReal ENNReal ProbabilityTheory Set in
theorem binomial_tail_sum_eq (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (n k : ℕ) : binomial_tail_prob p hp n k = ∑ i ∈ Finset.Ico k (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) := by
  classical
  set p_nn : ℝ≥0 := ⟨p, le_of_lt hp.1⟩ with hpnn_def
  have hp_le : p_nn ≤ 1 := le_of_lt hp.2
  let q := (PMF.binomial p_nn hp_le n).map (λ i => (i : ℕ))

  have h_supp : q.support ⊆ {x | x ≤ n} := binomial_pmf_map_support p_nn hp_le n

  unfold binomial_tail_prob
  dsimp only

  rw [pmf_tail_sum_finset _ n k h_supp]

  rw [ENNReal.toReal_sum]
  · have h_idx : Finset.Icc k n = Finset.Ico k (n + 1) := by
      ext x
      simp [Nat.lt_succ_iff]
    rw [h_idx]

    apply Finset.sum_congr rfl
    intro i hi
    have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_Ico.mp hi).2

    rw [pmf_binomial_apply_coe_le p_nn hp_le n i hi_le]

    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    rw [ENNReal.toReal_natCast]
    rw [ENNReal.toReal_pow]

    congr 1

    rw [ENNReal.toReal_pow]
    congr 1
    rw [ENNReal.toReal_sub_of_le]
    · simp only [ENNReal.toReal_one, ENNReal.coe_toReal]
      simp [hpnn_def]
    · exact_mod_cast hp_le
    · simp

  · intro i _
    apply ne_of_lt
    exact PMF.apply_lt_top _ i

open NNReal ENNReal ProbabilityTheory Set in
theorem pmf_tail_diff_eq_mass {p : PMF ℕ} (n k : ℕ) (_ : p.support ⊆ {x | x ≤ n}) : ENNReal.toReal (p.toMeasure (Set.Ici k)) - ENNReal.toReal (p.toMeasure (Set.Ici (k + 1))) = (p k).toReal := by
  let μ := p.toMeasure
  have h_split : Set.Ici k = {k} ∪ Set.Ici (k + 1) := by
    ext x
    simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases eq_or_lt_of_le h with rfl | h_lt
      · exact Or.inl rfl
      · exact Or.inr h_lt
    · rintro (rfl | h)
      · exact le_rfl
      · exact Nat.le_of_succ_le h

  have h_disj : Disjoint ({k} : Set ℕ) (Set.Ici (k + 1)) := by
    rw [Set.disjoint_left]
    intro x hx h_succ
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [Set.mem_Ici] at h_succ
    linarith

  have h_fin (s : Set ℕ) : μ s ≠ ∞ := MeasureTheory.measure_ne_top μ s
  have h_meas_s : MeasurableSet ({k} : Set ℕ) := measurableSet_singleton k
  have h_meas_Ici : MeasurableSet (Set.Ici (k + 1)) := measurableSet_Ici

  rw [h_split, MeasureTheory.measure_union h_disj h_meas_Ici]
  rw [ENNReal.toReal_add (h_fin _) (h_fin _)]
  rw [add_sub_cancel_right]
  rw [PMF.toMeasure_apply_singleton p k h_meas_s]

open NNReal ENNReal ProbabilityTheory Set in
theorem binomial_tail_prob_gt_n (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (n k : ℕ) (hk : n < k) : binomial_tail_prob p hp n k = 0 := by
  unfold binomial_tail_prob
  simp only
  let p_nn : NNReal := ⟨p, le_of_lt hp.1⟩
  let hp_le : p_nn ≤ 1 := le_of_lt hp.2
  let q := (PMF.binomial p_nn hp_le n).map (λ i => (i : ℕ))
  change (q.toMeasure (Set.Ici k)).toReal = 0
  have h_supp : q.support ⊆ {x | x ≤ n} := binomial_pmf_map_support p_nn hp_le n
  rw [pmf_tail_sum_finset q n k h_supp]
  rw [Finset.Icc_eq_empty_of_lt hk]
  simp

open Filter Topology Set in
theorem psi_def_continuousOn_Icc_to_half (k : ℕ) {a : ℝ} (ha : 0 < a) (_ : a < 1 / 2) : ContinuousOn (psi_def k) (Set.Icc a (1 / 2 : ℝ)) := by
  -- we obtain pointwise continuity on (0,1/2)
  have hIoo := psi_continuousOn_Ioo_zero_half k
  have hIoo_at : ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ), ContinuousAt (psi_def k) x := by
    have hopen : IsOpen (Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) := isOpen_Ioo
    exact (IsOpen.continuousOn_iff hopen).1 hIoo
  -- now use the definition of ContinuousOn
  intro x hx
  -- x lies in [a,1/2]
  have hx_le_half : x ≤ 1 / 2 := hx.2
  have hx_lt_or_eq : x < 1 / 2 ∨ x = 1 / 2 := lt_or_eq_of_le hx_le_half
  cases hx_lt_or_eq with
  | inl hx_lt_half =>
      -- interior point: 0 < x < 1/2, so use continuity on (0,1/2)
      have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
      have hx_mem_Ioo : x ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := ⟨hx_pos, hx_lt_half⟩
      have hcont_at : ContinuousAt (psi_def k) x := hIoo_at x hx_mem_Ioo
      -- continuous at x implies continuous within any set, in particular [a,1/2]
      exact hcont_at.continuousWithinAt
  | inr hx_eq_half =>
      -- endpoint x = 1/2: use the given continuity at 1/2
      have hcont_at_half : ContinuousWithinAt (psi_def k) (Set.Icc a (1 / 2 : ℝ)) (1 / 2 : ℝ) :=
        (psi_continuousAt_half k).continuousWithinAt
      simpa [hx_eq_half] using hcont_at_half

open Filter Topology Set in
lemma const_bound : (Real.sqrt 2 / 4) * (7/8 : ℝ) ^ (-(3/2 : ℝ)) ≤ (1 : ℝ) := by
  set C : ℝ := (Real.sqrt 2 / 4) * (7/8 : ℝ) ^ (-(3/2 : ℝ))
  -- C is positive
  have hC_pos : 0 < C := by
    have hpos1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hpos4 : 0 < (4 : ℝ) := by norm_num
    have hpos78 : 0 < (7/8 : ℝ) := by norm_num
    have hpos_pow : 0 < (7/8 : ℝ) ^ (-(3/2 : ℝ)) :=
      Real.rpow_pos_of_pos hpos78 _
    have hdiv : 0 < Real.sqrt 2 / 4 := div_pos hpos1 hpos4
    have hmul : 0 < (Real.sqrt 2 / 4) * (7/8 : ℝ) ^ (-(3/2 : ℝ)) :=
      mul_pos hdiv hpos_pow
    simpa [C] using hmul
  have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
  -- Compute C^2 explicitly as 64/343
  have hC_sq : C ^ 2 = (64 : ℝ) / 343 := by
    have hx : 0 ≤ (7/8 : ℝ) := le_of_lt (by norm_num : 0 < (7/8 : ℝ))
    -- ((7/8)^(-3/2))^2 = (7/8)^(-3)
    have h_rpow : ((7/8 : ℝ) ^ (-(3/2 : ℝ))) ^ 2 = (7/8 : ℝ) ^ (-3 : ℝ) := by
      have hmul := Real.rpow_mul hx (y := (-(3/2 : ℝ))) (z := (2 : ℝ))
      have : (-(3/2 : ℝ)) * 2 = (-3 : ℝ) := by ring
      simpa [this] using hmul.symm
    -- Expand C^2 using (ab)^2 = a^2 b^2
    have h1 : C ^ 2 = (Real.sqrt 2 / 4) ^ 2 * ((7/8 : ℝ) ^ (-(3/2 : ℝ))) ^ 2 := by
      simp [C, pow_two, mul_pow, mul_comm, mul_left_comm, mul_assoc]
    -- Replace the power of (7/8)
    have h2 : C ^ 2 = (Real.sqrt 2 / 4) ^ 2 * (7/8 : ℝ) ^ (-3 : ℝ) := by
      simpa [h_rpow] using h1
    -- Evaluate the (7/8)^(-3) part
    have h3 : (7/8 : ℝ) ^ (-3 : ℝ) = (512 : ℝ) / 343 := by
      norm_num
    -- Evaluate (sqrt 2 / 4)^2 = 1/8
    have h4 : (Real.sqrt 2 / 4 : ℝ) ^ 2 = (1 : ℝ) / 8 := by
      have hnonneg2 : 0 ≤ (2 : ℝ) := by norm_num
      have h_sqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
        simpa [pow_two] using Real.sq_sqrt hnonneg2
      calc
        (Real.sqrt 2 / 4 : ℝ) ^ 2
            = (Real.sqrt 2) ^ 2 / (4 : ℝ) ^ 2 := by
                  simpa [div_pow]
        _ = (2 : ℝ) / (4 : ℝ) ^ 2 := by simp [h_sqrt]
        _ = 2 / 16 := by norm_num
        _ = (1 : ℝ) / 8 := by norm_num
    -- Put everything together
    calc
      C ^ 2
          = (Real.sqrt 2 / 4) ^ 2 * (7/8 : ℝ) ^ (-3 : ℝ) := h2
      _ = ((1 : ℝ) / 8) * ((512 : ℝ) / 343) := by simpa [h3, h4]
      _ = (64 : ℝ) / 343 := by norm_num
  -- From C^2 ≤ 1, deduce C ≤ 1 using nonnegativity of C
  have hCsq_le : C ^ 2 ≤ (1 : ℝ) := by
    have : (64 : ℝ) / 343 ≤ (1 : ℝ) := by norm_num
    simpa [hC_sq] using this
  have hC_le_one : C ≤ (1 : ℝ) := by
    -- Real.sq_le (h : 0 ≤ y) : x^2 ≤ y ↔ -√y ≤ x ∧ x ≤ √y
    have h' := (Real.sq_le (by norm_num : (0 : ℝ) ≤ (1 : ℝ))).1 hCsq_le
    have hC_le : C ≤ Real.sqrt 1 := h'.2
    simpa using hC_le
  simpa [C] using hC_le_one

open Filter Topology Set in
theorem deriv_function_A_bound (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/8)) : |deriv function_A p| ≤ p^(-(3 : ℝ)/2) := by
  -- Basic bounds on p
  have h_pos : 0 < p := hp.1
  have h_bound : p < (1/8 : ℝ) := hp.2
  have h_lt_one : p < 1 := by linarith
  have hp_mem : p ∈ Set.Ioo 0 1 := ⟨h_pos, h_lt_one⟩

  -- Use the derivative formula from the lemma
  have h_deriv_at := hasDerivAt_function_A p hp_mem
  have h_deriv : deriv function_A p = -(Real.sqrt 2) / (4 * (p * (1 - p)) ^ (3/2 : ℝ)) :=
    h_deriv_at.deriv

  -- Positivity of p*(1-p) and the denominator
  have h_inner_pos : 0 < p * (1 - p) := by
    have h1 : 0 < 1 - p := sub_pos.mpr h_lt_one
    exact _root_.mul_pos h_pos h1

  have h_denom_pos : 0 < 4 * (p * (1 - p)) ^ (3/2 : ℝ) := by
    have h_rpow_pos : 0 < (p * (1 - p)) ^ (3/2 : ℝ) :=
      Real.rpow_pos_of_pos h_inner_pos _
    have : 0 < (4 : ℝ) * (p * (1 - p)) ^ (3/2 : ℝ) := mul_pos (by norm_num) h_rpow_pos
    simpa [mul_comm] using this

  -- Express |deriv| using explicit formula
  have h_abs_eq : |deriv function_A p|
      = |-(Real.sqrt 2) / (4 * (p * (1 - p)) ^ (3/2 : ℝ))| := by
    simpa [h_deriv]

  -- Simplify absolute value
  have h_abs_simpl :
      |-(Real.sqrt 2) / (4 * (p * (1 - p)) ^ (3/2 : ℝ))|
        = Real.sqrt 2 / (4 * (p * (1 - p)) ^ (3/2 : ℝ)) := by
    have hden : 0 < 4 * (p * (1 - p)) ^ (3/2 : ℝ) := h_denom_pos
    have hden_abs : |4 * (p * (1 - p)) ^ (3/2 : ℝ)| = 4 * (p * (1 - p)) ^ (3/2 : ℝ) :=
      abs_of_pos hden
    calc
      |-(Real.sqrt 2) / (4 * (p * (1 - p)) ^ (3/2 : ℝ))|
          = |-(Real.sqrt 2)| / |4 * (p * (1 - p)) ^ (3/2 : ℝ)| := by
              simpa [abs_div]
      _ = Real.sqrt 2 / (4 * (p * (1 - p)) ^ (3/2 : ℝ)) := by
        have : |-(Real.sqrt 2)| = Real.sqrt 2 := by
          simpa using (abs_neg (Real.sqrt 2))
        simpa [this, hden_abs]

  have h_main_eq : |deriv function_A p|
      = Real.sqrt 2 / (4 * (p * (1 - p)) ^ (3/2 : ℝ)) := by
    simpa [h_abs_eq, h_abs_simpl]

  -- Express 1 / (p*(1-p))^(3/2) using negative powers
  have h_inv_pow : 1 / (p * (1 - p)) ^ (3/2 : ℝ)
      = (p * (1 - p)) ^ (-(3/2 : ℝ)) := by
    have h' := Real.rpow_neg (le_of_lt h_inner_pos) (3/2 : ℝ)
    calc
      1 / (p * (1 - p)) ^ (3/2 : ℝ)
          = ((p * (1 - p)) ^ (3/2 : ℝ))⁻¹ := by
                simp [one_div]
      _ = (p * (1 - p)) ^ (-(3/2 : ℝ)) := by simpa [h']

  -- Factor (p*(1-p))^(-3/2) as p^(-3/2)*(1-p)^(-3/2)
  have h_rpow_neg_mul : (p * (1 - p)) ^ (-(3/2 : ℝ))
      = p ^ (-(3/2 : ℝ)) * (1 - p) ^ (-(3/2 : ℝ)) := by
    have h :=
      (Real.mul_rpow (x := p) (y := 1 - p) (z := (-(3/2 : ℝ)))
        (le_of_lt h_pos) (le_of_lt (sub_pos.mpr h_lt_one)))
    simpa [mul_comm] using h

  -- Now express |deriv| as (sqrt2/4)*(1-p)^(-3/2)*p^(-3/2)
  have h_eq2 : |deriv function_A p|
      = (Real.sqrt 2 / 4) * (1 - p) ^ (-(3/2 : ℝ)) * p ^ (-(3/2 : ℝ)) := by
    calc
      |deriv function_A p|
          = Real.sqrt 2 / (4 * (p * (1 - p)) ^ (3/2 : ℝ)) := h_main_eq
      _ = (Real.sqrt 2 / 4) * (1 / (p * (1 - p)) ^ (3/2 : ℝ)) := by
            field_simp [div_eq_mul_inv]
      _ = (Real.sqrt 2 / 4) * (p * (1 - p)) ^ (-(3/2 : ℝ)) := by
            simpa [h_inv_pow]
      _ = (Real.sqrt 2 / 4) * (p ^ (-(3/2 : ℝ)) * (1 - p) ^ (-(3/2 : ℝ))) := by
            simpa [h_rpow_neg_mul]
      _ = (Real.sqrt 2 / 4) * (1 - p) ^ (-(3/2 : ℝ)) * p ^ (-(3/2 : ℝ)) := by
            ring

  -- Lower bound on 1 - p
  have h_one_sub_ge : (7/8 : ℝ) ≤ 1 - p := by
    have hp_le : p ≤ (1/8 : ℝ) := le_of_lt h_bound
    have : 1 - p ≥ 7/8 := by linarith
    simpa [ge_iff_le] using this

  -- Since exponent is negative, larger base gives smaller value
  have h_pow_le : (1 - p) ^ (-(3/2 : ℝ)) ≤ (7/8 : ℝ) ^ (-(3/2 : ℝ)) := by
    have h_nonpos : (-(3/2 : ℝ)) ≤ 0 := by norm_num
    have h7pos : 0 < (7/8 : ℝ) := by norm_num
    have h7_le_1p : (7/8 : ℝ) ≤ 1 - p := h_one_sub_ge
    have :=
      (Real.rpow_le_rpow_of_nonpos (x := (7/8 : ℝ)) (y := 1 - p)
        (z := (-(3/2 : ℝ))) h7pos h7_le_1p h_nonpos)
    simpa using this

  -- Numeric constant bound from the helper lemma
  have h_const_le_one := const_bound

  -- Combine these bounds: (sqrt2/4)*(1-p)^(-3/2) ≤ 1
  have h_le_const :
      (Real.sqrt 2 / 4) * (1 - p) ^ (-(3/2 : ℝ)) ≤ 1 := by
    have h_nonneg_const : 0 ≤ Real.sqrt 2 / 4 := by
      have hpos1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hpos4 : 0 < (4 : ℝ) := by norm_num
      exact le_of_lt (div_pos hpos1 hpos4)
    have h1 : (Real.sqrt 2 / 4) * (1 - p) ^ (-(3/2 : ℝ))
        ≤ (Real.sqrt 2 / 4) * (7/8 : ℝ) ^ (-(3/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left h_pow_le h_nonneg_const
    exact le_trans h1 h_const_le_one

  -- Final: multiply by positive p^(-3/2)
  have h_p_pow_pos : 0 < p ^ (-(3/2 : ℝ)) :=
    Real.rpow_pos_of_pos h_pos _
  have h_p_pow_nonneg : 0 ≤ p ^ (-(3/2 : ℝ)) := le_of_lt h_p_pow_pos
  calc
    |deriv function_A p|
        = (Real.sqrt 2 / 4) * (1 - p) ^ (-(3/2 : ℝ)) * p ^ (-(3/2 : ℝ)) := h_eq2
    _ ≤ 1 * p ^ (-(3/2 : ℝ)) := by
          have := mul_le_mul_of_nonneg_right h_le_const h_p_pow_nonneg
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
    _ = p ^ (-(3/2 : ℝ)) := by ring
    _ = p ^ (-(3 : ℝ) / 2) := by ring_nf

open Set in
theorem z_deriv_neg (k : ℕ) (hk : 0 < k) (p : ℝ) (hp : p ∈ Set.Ioo 0 (1 / 2)) :
  let s := p * (1 - p)
  let z' := -Real.sqrt (2 * (k : ℝ)) / (4 * s ^ (3 / 2 : ℝ))
  HasDerivAt
    (fun x => (1 / 2 - x) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (x * (1 - x)))
    z' p ∧
  z' < 0 := by
  let s := p * (1 - p)
  let z' := -Real.sqrt (2 * (k : ℝ)) / (4 * s ^ (3 / 2 : ℝ))

  have hp_01 : p ∈ Ioo 0 1 := by
    rcases hp with ⟨h1, h2⟩
    constructor <;> linarith

  have h_deriv_A := hasDerivAt_function_A p hp_01

  let c := Real.sqrt k
  let f := fun x => (1 / 2 - x) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (x * (1 - x))

  have h_sqrt_k_2 : Real.sqrt k * Real.sqrt 2 = Real.sqrt (2 * k) := by
    rw [mul_comm 2 (k:ℝ), Real.sqrt_mul]
    ring_nf
    exact Nat.cast_nonneg k

  have h_alg : ∀ x, f x = c * function_A x := by
    intro x
    unfold f function_A c
    field_simp
    rw [mul_assoc (1 - 2*x) (Real.sqrt k)]
    rw [h_sqrt_k_2]

  have h_deriv : HasDerivAt f (c * (-(Real.sqrt 2) / (4 * s ^ (3/2 : ℝ)))) p := by
    apply HasDerivAt.congr_of_eventuallyEq (HasDerivAt.const_mul c h_deriv_A)
    filter_upwards with x
    exact h_alg x

  have h_val_eq : c * (-(Real.sqrt 2) / (4 * s ^ (3/2 : ℝ))) = z' := by
    dsimp [z', c, s]
    field_simp
    rw [← h_sqrt_k_2]

  rw [h_val_eq] at h_deriv

  have h_neg : z' < 0 := by
    dsimp [z', s]
    have hs : 0 < p * (1 - p) := by
      rcases hp with ⟨h1, h2⟩
      apply mul_pos h1
      linarith
    apply div_neg_of_neg_of_pos
    · rw [neg_lt_zero]
      apply Real.sqrt_pos.mpr
      norm_cast
      linarith
    · apply _root_.mul_pos
      · norm_num
      · apply Real.rpow_pos_of_pos hs

  exact ⟨h_deriv, h_neg⟩

open Set in
theorem function_A_sq_bound (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/8)) : (function_A p)^2 ≥ 1 / (4 * p) := by
  rcases hp with ⟨hp_pos, hp_lt_1_8⟩
  have hp_lt_one : p < 1 := by
    have : (1 / 8 : ℝ) < 1 := by norm_num
    exact lt_trans hp_lt_1_8 this
  -- define s = p * (1 - p)
  set s : ℝ := p * (1 - p) with hs_def
  have hs_pos : 0 < s := by
    unfold s
    exact _root_.mul_pos hp_pos (sub_pos.mpr hp_lt_one)
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  -- use the given identity for (function_A p)^2
  have hA : (function_A p) ^ 2 = 1 / (2 * s) - 2 := by
    have := function_A_sq_identity p (by exact And.intro hp_pos hp_lt_one)
    simpa [s, hs_def] using this
  -- Prove the inequality in terms of s and p
  have hineq_fracs : 1 / (4 * p) ≤ 1 / (2 * s) - 2 := by
    have hp0 : 0 < p := hp_pos
    have hp8 : p < 1 / 8 := hp_lt_1_8
    have hs0 : 0 < s := hs_pos
    -- Clear denominators and reduce to a polynomial inequality in p.
    field_simp [s, hs_def, hp_ne, hs_ne]
    -- Now the goal is a polynomial inequality; solve with nlinarith.
    nlinarith
  -- Translate back to (function_A p)^2 using hA.
  have : 1 / (4 * p) ≤ (function_A p) ^ 2 := by
    simpa [hA] using hineq_fracs
  exact this

open Set in
theorem R_aux_log_eq (z : ℝ) : L_aux z = Real.log (R_aux z) := by
  unfold L_aux R_aux
  -- Now goal: log(2/sqrt(pi)) - z^2 + 3/2 * log(z^2+1) = log(2/sqrt(pi) * exp(-z^2) * (z^2+1)^(3/2)).
  -- Work from right to left.
  symm
  -- Some auxiliary positivity / nonvanishing facts
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 := by
    -- from positivity of sqrt(pi)
    have hsqrt_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ_pos
    exact ne_of_gt hsqrt_pos
  have hconst_ne : (2 / Real.sqrt Real.pi : ℝ) ≠ 0 := by
    have h2_ne : (2 : ℝ) ≠ 0 := two_ne_zero
    exact div_ne_zero h2_ne hsqrt_ne
  have hexp_ne : Real.exp (-z ^ 2) ≠ 0 := Real.exp_ne_zero _
  have hmul_ne : (2 / Real.sqrt Real.pi * Real.exp (-z ^ 2) : ℝ) ≠ 0 :=
    mul_ne_zero hconst_ne hexp_ne
  -- base positivity for z^2 + 1
  have hbase_pos : 0 < z ^ 2 + 1 := by
    have hz2_nonneg : 0 ≤ z ^ 2 := by
      have := sq_nonneg z
      simpa using this
    have h1_pos : (0 : ℝ) < 1 := by norm_num
    exact add_pos_of_nonneg_of_pos hz2_nonneg h1_pos
  have hpow_ne : (z ^ 2 + 1) ^ (3 / 2 : ℝ) ≠ 0 := by
    have hpow_pos : 0 < (z ^ 2 + 1) ^ (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hbase_pos _
    exact ne_of_gt hpow_pos
  have hlogpow :
      Real.log ((z ^ 2 + 1) ^ (3 / 2 : ℝ)) =
        (3 / 2 : ℝ) * Real.log (z ^ 2 + 1) :=
    Real.log_rpow hbase_pos (3 / 2 : ℝ)
  -- First use log_mul on the triple product, grouping as (const*exp)*power
  calc
    Real.log (2 / Real.sqrt Real.pi * Real.exp (-z ^ 2) *
        (z ^ 2 + 1) ^ (3 / 2 : ℝ))
        = Real.log ((2 / Real.sqrt Real.pi * Real.exp (-z ^ 2)) *
            (z ^ 2 + 1) ^ (3 / 2 : ℝ)) := by
              simp [mul_assoc]
    _ = Real.log (2 / Real.sqrt Real.pi * Real.exp (-z ^ 2)) +
          Real.log ((z ^ 2 + 1) ^ (3 / 2 : ℝ)) := by
              simpa using Real.log_mul hmul_ne hpow_ne
    _ = (Real.log (2 / Real.sqrt Real.pi) +
          Real.log (Real.exp (-z ^ 2))) +
          Real.log ((z ^ 2 + 1) ^ (3 / 2 : ℝ)) := by
            -- apply log_mul to the first factor (const * exp)
            have hlogA :
              Real.log (2 / Real.sqrt Real.pi * Real.exp (-z ^ 2)) =
                Real.log (2 / Real.sqrt Real.pi) + Real.log (Real.exp (-z ^ 2)) :=
              Real.log_mul hconst_ne hexp_ne
            simpa [hlogA]
    _ = Real.log (2 / Real.sqrt Real.pi) - z ^ 2 +
          (3 / 2 : ℝ) * Real.log (z ^ 2 + 1) := by
            -- simplify log(exp) and log of power, and rearrange
            have : Real.log (Real.exp (-z ^ 2)) = -z ^ 2 := by
              simpa using (Real.log_exp (-z ^ 2))
            simp [this, hlogpow, sub_eq_add_neg, add_comm, add_left_comm,
                  add_assoc]

open Filter Topology in
theorem tendsto_linear_sub_log_atTop_v2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Filter.Tendsto (fun t : ℝ => a * t - b * Real.log t) Filter.atTop Filter.atTop := by
  exact tendsto_linear_sub_log_atTop a b ha hb

open Filter Topology in
theorem psi_closed_form (k : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo 0 (1 / 2)) :
  let s : ℝ := p * (1 - p);
  let z : ℝ := (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt s;
  let psi : ℝ := z ^ 2 / 2 + (k + 1 / 2 : ℝ) * Real.log s;
  psi = (k : ℝ) / (4 * s) - (k : ℝ) + (k + 1 / 2 : ℝ) * Real.log s := by
  intro s z psi
  dsimp [psi, s, z] at *
  have hz := z_sq_expression k p hp
  dsimp at hz
  -- substitute z^2 using hz
  rw [hz]
  -- now show algebraic identity
  have hp_pos : 0 < p := hp.1
  have hp_lt : p < (1 / 2 : ℝ) := hp.2
  have hs_pos : 0 < p * (1 - p) := by
    have h1 : 0 < 1 - p := by
      have hlt1 : p < (1 : ℝ) := lt_trans hp_lt (by norm_num)
      exact sub_pos.mpr hlt1
    exact _root_.mul_pos hp_pos h1
  have h2 : ((k : ℝ) / (2 * (p * (1 - p))) - 2 * (k : ℝ)) / 2 = (k : ℝ) / (4 * (p * (1 - p))) - (k : ℝ) := by
    field_simp [hs_pos.ne']
    ring
  -- finish by rewriting using h2
  have := congrArg (fun t => t + (k + 1 / 2 : ℝ) * Real.log (p * (1 - p))) h2
  -- now goal is exactly this equality up to associativity/commutativity of addition and subtraction
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using this

open ProbabilityTheory Set in
theorem deriv_binomial_tail_prob (n k : ℕ) (p : ℝ) (_ : 0 < k) : deriv (fun x => binomial_tail_integral n k x) p = (n.choose k : ℝ) * k * p^(k-1) * (1-p)^(n-k) := by
  dsimp [binomial_tail_integral]
  let C := (n.choose k : ℝ) * k
  let f := fun t : ℝ => t^(k-1) * (1-t)^(n-k)
  have hf : Continuous f := by
    apply Continuous.mul
    · apply continuous_pow
    · apply Continuous.pow
      apply Continuous.sub
      · exact continuous_const
      · exact continuous_id
  rw [deriv_const_mul]
  · rw [Continuous.deriv_integral f hf 0 p]
    simp [f]
    ring
  · -- need differentiability of integral
    apply Differentiable.differentiableAt
    apply intervalIntegral.differentiable_integral_of_continuous
    exact hf

open ProbabilityTheory Set in
theorem deriv_correction_term (k : ℕ) (_ : 0 < k) (p : ℝ) (hp : p ∈ Set.Ioo 0 1) : deriv (fun y => (1 / 2 : ℝ) * ((2 * k).choose k) * (Real.sqrt (y * (1 - y))) ^ (2 * k)) p = (1 / 2) * ((2 * k).choose k : ℝ) * k * (p * (1 - p)) ^ (k - 1) * (1 - 2 * p) := by
  let C : ℝ := (1 / 2 : ℝ) * ((2 * k).choose k : ℝ)

  have h_inner : HasDerivAt (fun y => y * (1 - y)) (1 - 2 * p) p := hasDerivAt_y_mul_one_sub_y p

  have h_poly : HasDerivAt (fun y => (y * (1 - y)) ^ k) (k * (p * (1 - p)) ^ (k - 1) * (1 - 2 * p)) p := by
    simpa using h_inner.pow k

  have h_poly_C : HasDerivAt (fun y => C * (y * (1 - y)) ^ k) (C * (k * (p * (1 - p)) ^ (k - 1) * (1 - 2 * p))) p :=
    h_poly.const_mul C

  have h_eventually : (fun y => C * (Real.sqrt (y * (1 - y))) ^ (2 * k)) =ᶠ[nhds p] (fun y => C * (y * (1 - y)) ^ k) := by
    have h_cont : ContinuousAt (fun y => y * (1 - y)) p := by
      fun_prop
    have h_pos : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
    have h_nhds : ∀ᶠ y in nhds p, 0 ≤ y * (1 - y) := by
      apply h_cont.eventually
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi h_pos] with x hx
      exact le_of_lt hx
    filter_upwards [h_nhds] with y hy
    rw [pow_sqrt_sq_eq k (y * (1 - y)) hy]

  have h_deriv_at : HasDerivAt (fun y => C * (Real.sqrt (y * (1 - y))) ^ (2 * k)) (C * (k * (p * (1 - p)) ^ (k - 1) * (1 - 2 * p))) p :=
    h_poly_C.congr_of_eventuallyEq h_eventually

  rw [h_deriv_at.deriv]
  dsimp [C]
  ring

open ProbabilityTheory Set in
theorem binomial_tail_integral_tendsto_zero (k : ℕ) (_ : 0 < k) : Filter.Tendsto (fun p : ℝ => binomial_tail_integral (2 * k) k p) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  dsimp [binomial_tail_integral]
  let f := fun (t : ℝ) => t^(k-1) * (1-t)^(2*k-k)
  let C : ℝ := (2 * k).choose k * k
  let I := fun (p : ℝ) => ∫ t in (0:ℝ)..p, f t

  change Filter.Tendsto (fun p => C * I p) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

  have h_cont_f : Continuous f := by
    apply Continuous.mul
    · apply Continuous.pow continuous_id
    · apply Continuous.pow
      apply Continuous.sub continuous_const continuous_id

  have h_cont_I : Continuous I := by
    apply intervalIntegral.continuous_primitive
    intro a b
    exact Continuous.intervalIntegrable h_cont_f a b

  have h_lim_I : Filter.Tendsto I (nhds 0) (nhds 0) := by
    have h := Continuous.tendsto h_cont_I 0
    rw [show I 0 = 0 by simp [I]] at h
    exact h

  have h_total : Filter.Tendsto (fun p => C * I p) (nhds 0) (nhds (C * 0)) :=
    Filter.Tendsto.const_mul C h_lim_I

  rw [mul_zero] at h_total

  apply Filter.Tendsto.mono_left h_total
  exact nhdsWithin_le_nhds

open ProbabilityTheory Set in
theorem gaussian_core_pointwise_bound {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) (4/3 : ℝ)) : (2 : ℝ) ≤ gaussian_core_fun u := by
  have hmono : gaussian_core_fun 1 ≤ gaussian_core_fun u :=
    gaussian_core_fun_mono
      (by
        constructor <;> linarith)
      hu
      hu.left
  simpa [gaussian_core_fun] using hmono

open ProbabilityTheory in
theorem gaussian_cdf_lipschitz: LipschitzWith (Real.toNNReal (1 / Real.sqrt (2 * Real.pi))) (cdf (gaussianReal 0 1)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact differentiable_cdf_gaussianReal
  · intro x
    rw [gaussian_cdf_deriv]
    let C := 1 / Real.sqrt (2 * Real.pi)
    have hC_nonneg : 0 ≤ C := by
      apply div_nonneg zero_le_one
      apply Real.sqrt_nonneg
    rw [Real.le_toNNReal_iff_coe_le hC_nonneg]
    simp only [coe_nnnorm]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x)]
    exact gaussian_pdf_bound x

open ProbabilityTheory in
theorem gaussian_tail_bound_h_properties (p : ℝ) (hp : p ∈ Set.Ico (1/4) (1/2)) : let h := fun x => cdf (gaussianReal 0 1) (function_A x) - (1 - x); ContinuousOn h (Set.Icc p (1/2)) ∧ DifferentiableOn ℝ h (Set.Ioo p (1/2)) := by
  let h := fun x => cdf (gaussianReal 0 1) (function_A x) - (1 - x)
  have h_diff_cdf : Differentiable ℝ (fun x => cdf (gaussianReal 0 1) x) := differentiable_cdf_gaussianReal

  have subset_oo : Set.Ioo p (1/2) ⊆ Set.Ioo (1/4) (1/2) := by
    intro x hx
    simp at hx
    simp
    constructor
    · linarith [hp.1]
    · exact hx.2

  have subset_cc : Set.Icc p (1/2) ⊆ Set.Icc (1/4) (1/2) := by
    intro x hx
    simp at hx
    simp
    constructor
    · linarith [hp.1]
    · exact hx.2

  constructor
  · apply ContinuousOn.sub
    · apply ContinuousOn.comp h_diff_cdf.continuous.continuousOn (function_A_properties.1.mono subset_cc)
      exact Set.mapsTo_univ _ _
    · apply ContinuousOn.sub continuousOn_const continuousOn_id

  · apply DifferentiableOn.sub
    · apply DifferentiableOn.comp h_diff_cdf.differentiableOn (function_A_properties.2.mono subset_oo)
      exact Set.mapsTo_univ _ _
    · apply DifferentiableOn.sub (differentiableOn_const (1:ℝ)) differentiableOn_id

open ProbabilityTheory in
theorem function_A_comp_cdf_differentiable (x : ℝ) (hx : x ∈ Set.Ioo (1/4) (1/2)) : DifferentiableAt ℝ (fun y => cdf (gaussianReal 0 1) (function_A y)) x := by
  have hA_on : DifferentiableOn ℝ function_A (Set.Ioo (1 / 4) (1 / 2)) :=
    function_A_properties.2
  have h_open : IsOpen (Set.Ioo (1 / 4 : ℝ) (1 / 2)) := isOpen_Ioo
  have hA_at : DifferentiableAt ℝ function_A x := by
    apply hA_on.differentiableAt
    apply IsOpen.mem_nhds h_open hx
  have h_cdf : Differentiable ℝ (fun z => cdf (gaussianReal 0 1) z) := differentiable_cdf_gaussianReal
  apply DifferentiableAt.comp
  · exact h_cdf (function_A x)
  · exact hA_at

open ProbabilityTheory in
theorem gaussian_deriv_comp_A (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/2)) : deriv (fun x => ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (function_A x)) p = ProbabilityTheory.gaussianPDFReal 0 1 (function_A p) * deriv function_A p := by
  -- Differentiability of A at p
  have h_diff_A : DifferentiableAt ℝ function_A p := by
    unfold function_A
    apply DifferentiableAt.div
    · apply DifferentiableAt.mul
      · apply DifferentiableAt.sub
        · apply differentiableAt_const
        · apply differentiableAt_id
      · apply differentiableAt_const
    · apply DifferentiableAt.sqrt
      · apply DifferentiableAt.mul
        · apply differentiableAt_id
        · apply DifferentiableAt.sub
          · apply differentiableAt_const
          · apply differentiableAt_id
      · apply ne_of_gt
        apply _root_.mul_pos
        · exact hp.1
        · linarith [hp.2]
    · apply ne_of_gt
      apply Real.sqrt_pos.mpr
      apply _root_.mul_pos
      · exact hp.1
      · linarith [hp.2]

  let cdf_g := (fun x => ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x)
  have h_diff_cdf : DifferentiableAt ℝ cdf_g (function_A p) := by
    apply differentiableAt_of_deriv_ne_zero
    rw [(gaussian_calculus_helpers (function_A p)).1]
    rw [ProbabilityTheory.gaussianPDFReal_def]
    apply ne_of_gt
    apply _root_.mul_pos
    · apply inv_pos.mpr
      apply Real.sqrt_pos.mpr
      apply _root_.mul_pos
      · norm_num
        exact Real.pi_pos
      · norm_num
    · apply Real.exp_pos

  have eq_chain := deriv_comp (x:=p) h_diff_cdf h_diff_A

  change deriv (cdf_g ∘ function_A) p = _
  rw [eq_chain]
  dsimp [cdf_g]
  rw [(gaussian_calculus_helpers (function_A p)).1]

open ProbabilityTheory in
lemma gaussian_scaled_deriv (x : ℝ) :
  2 * (ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2) * Real.sqrt 2)
    = 2 / Real.sqrt Real.pi * Real.exp (-x^2) := by
  -- use the standard form of the Gaussian pdf
  have h_pdf := gaussianPDFReal_std (x * Real.sqrt 2)
  -- rewrite the pdf
  have hpdf' : ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x * Real.sqrt 2) ^ 2 / 2) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_pdf
  -- substitute into the left-hand side
  calc
    2 * (ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2) * Real.sqrt 2)
        = 2 * ((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-(x * Real.sqrt 2) ^ 2 / 2) *
                Real.sqrt 2) := by
          simp [hpdf', mul_comm, mul_left_comm, mul_assoc]
    _ = 2 * (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt 2 *
          Real.exp (-(x * Real.sqrt 2) ^ 2 / 2) := by
          ring_nf
    -- simplify the exponent: (x * √2)^2 / 2 = x^2
    _ = 2 * (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt 2 *
          Real.exp (-x^2) := by
          -- show equality of exponents
          have h_exp_arg : -(x * Real.sqrt 2) ^ 2 / 2 = -x^2 := by
            -- (sqrt 2)^2 = 2
            have h_sqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
              have h2 : (0 : ℝ) ≤ 2 := by norm_num
              have hmul : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
                simpa using Real.mul_self_sqrt h2
              simpa [pow_two, mul_comm] using hmul
            -- expand (x * √2)^2
            have h_sq : (x * Real.sqrt 2) ^ 2 = x^2 * 2 := by
              calc
                (x * Real.sqrt 2) ^ 2
                    = x^2 * (Real.sqrt 2) ^ 2 := by
                        simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
                _ = x^2 * 2 := by simpa [h_sqrt2]
            -- cancel the factor 2 in the denominator
            have hx : (x^2 * (2 : ℝ)) / 2 = x^2 := by
              simpa using (mul_div_cancel_right (x^2) (2 : ℝ))
            calc
              -(x * Real.sqrt 2) ^ 2 / 2
                  = -((x * Real.sqrt 2) ^ 2 / 2) := by
                        simp [neg_div]
              _ = -((x^2 * 2) / 2) := by
                        simp [h_sq]
              _ = -x^2 := by
                        simpa [hx]
          -- use equality of exponent arguments
          simpa [h_exp_arg]
    -- rewrite sqrt(2π) as sqrt 2 * sqrt π
    _ = 2 * (Real.sqrt 2 * Real.sqrt Real.pi)⁻¹ * Real.sqrt 2 *
          Real.exp (-x^2) := by
          have h_sqrt :
            Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
              have h2 : (0 : ℝ) ≤ 2 := by norm_num
              have hpi : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (Real.sqrt_mul (a := (2 : ℝ)) (b := Real.pi) h2 hpi)
          simp [h_sqrt]
    -- simplify the constant factor 2 * (sqrt (2π))⁻¹ * sqrt 2
    _ = 2 / Real.sqrt Real.pi * Real.exp (-x^2) := by
          have h2pos : (0 : ℝ) < Real.sqrt 2 := by
            have h2 : (0 : ℝ) < 2 := by norm_num
            exact Real.sqrt_pos.mpr h2
          have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt h2pos
          have h_inv :
            (Real.sqrt 2 * Real.sqrt Real.pi)⁻¹
              = (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ := by
            simpa using
              (mul_inv_rev (Real.sqrt 2) (Real.sqrt Real.pi))
          calc
            2 * (Real.sqrt 2 * Real.sqrt Real.pi)⁻¹ * Real.sqrt 2 *
                Real.exp (-x^2)
                = 2 * ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
                    Real.sqrt 2 * Real.exp (-x^2) := by
                  simp [h_inv, mul_comm, mul_left_comm, mul_assoc]
            _ = (2 * (Real.sqrt Real.pi)⁻¹ *
                    ((Real.sqrt 2)⁻¹ * Real.sqrt 2)) *
                  Real.exp (-x^2) := by
                  ac_rfl
            _ = (2 * (Real.sqrt Real.pi)⁻¹ * 1) *
                  Real.exp (-x^2) := by
                  simp [h2ne]
            _ = 2 * (Real.sqrt Real.pi)⁻¹ *
                  Real.exp (-x^2) := by
                  simp [mul_comm, mul_left_comm, mul_assoc]
            _ = 2 / Real.sqrt Real.pi *
                  Real.exp (-x^2) := by
                  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

open ProbabilityTheory in
theorem gaussian_tail_region2_g_hasDeriv (x : ℝ) : HasDerivAt (fun z : ℝ => (1 - z / Real.sqrt (z^2 + 1)) - 2 * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (z * Real.sqrt 2))) (2 / Real.sqrt Real.pi * Real.exp (-x^2) - 1 / (x^2 + 1) ^ (3/2 : ℝ)) x := by
  classical
  -- Define F(z) = Φ(z * √2)
  let F : ℝ → ℝ := fun t =>
    ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (t * Real.sqrt 2)

  -- Derivative of the rational term 1 - z / √(z^2 + 1)
  have h_rational : HasDerivAt (fun t : ℝ => 1 - t / Real.sqrt (t^2 + 1))
      (-(1 / (x^2 + 1) ^ (3/2 : ℝ))) x := by
    have hz : HasDerivAt (fun t : ℝ => t / Real.sqrt (t^2 + 1))
        (1 / (x^2 + 1) ^ (3/2 : ℝ)) x := hasDerivAt_z_div_sqrt x
    -- derivative of 1 - f is -f'
    simpa using hz.const_sub 1

  -- Derivative of F
  have hF : HasDerivAt F (ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2) * Real.sqrt 2) x :=
    hasDerivAt_gaussian_cdf_scaled x

  -- Derivative of 1 - F t
  have h_one_minus_F : HasDerivAt (fun t : ℝ => 1 - F t)
      (-(ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2) * Real.sqrt 2)) x := by
    simpa using hF.const_sub 1

  -- Derivative of -2 * (1 - F t)
  have h_tail : HasDerivAt (fun t : ℝ => -2 * (1 - F t))
      (2 * (ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2) * Real.sqrt 2)) x := by
    have h := h_one_minus_F.const_mul (-2)
    -- simplify the constant factor -2 * -(⋯) = 2 * ⋯
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

  -- Combine: g z = (1 - z/√(z^2+1)) - 2 * (1 - F z)
  --          = (1 - z/√(z^2+1)) + (-2 * (1 - F z))
  have h_combined_raw : HasDerivAt
      (fun z : ℝ => (1 - z / Real.sqrt (z^2 + 1)) + (-2 * (1 - F z)))
      (-(1 / (x^2 + 1) ^ (3/2 : ℝ)) +
        2 * (ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2) * Real.sqrt 2)) x := by
    simpa using h_rational.add h_tail

  -- Simplify the derivative value using the explicit Gaussian pdf
  have h_simp_deriv :
      (-((x^2 + 1) ^ (3/2 : ℝ))⁻¹ +
        2 * (ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2) * Real.sqrt 2))
        = 2 / Real.sqrt Real.pi * Real.exp (-x^2)
            - ((x^2 + 1) ^ (3/2 : ℝ))⁻¹ := by
    -- first, use the helper lemma for the Gaussian pdf term
    have h1 :
      (-((x^2 + 1) ^ (3/2 : ℝ))⁻¹ +
          2 * (ProbabilityTheory.gaussianPDFReal 0 1 (x * Real.sqrt 2) * Real.sqrt 2))
        =
        -((x^2 + 1) ^ (3/2 : ℝ))⁻¹ +
          2 / Real.sqrt Real.pi * Real.exp (-x^2) := by
      have h_gauss := gaussian_scaled_deriv x
      simpa [h_gauss, one_div]  -- only change the Gaussian term
    -- then, reorder terms to match the target expression
    have h2 :
      (-((x^2 + 1) ^ (3/2 : ℝ))⁻¹ +
          2 / Real.sqrt Real.pi * Real.exp (-x^2))
        = 2 / Real.sqrt Real.pi * Real.exp (-x^2)
            - ((x^2 + 1) ^ (3/2 : ℝ))⁻¹ := by
      calc
        (-((x^2 + 1) ^ (3/2 : ℝ))⁻¹ +
            2 / Real.sqrt Real.pi * Real.exp (-x^2))
            = 2 / Real.sqrt Real.pi * Real.exp (-x^2)
                + (-((x^2 + 1) ^ (3/2 : ℝ))⁻¹) := by
              ac_rfl
        _ = 2 / Real.sqrt Real.pi * Real.exp (-x^2)
                - ((x^2 + 1) ^ (3/2 : ℝ))⁻¹ := by
              simp [sub_eq_add_neg]
    exact h1.trans h2

  -- Apply the simplification of the derivative
  have h_final' : HasDerivAt
      (fun z : ℝ => (1 - z / Real.sqrt (z^2 + 1)) + (-2 * (1 - F z)))
      (2 / Real.sqrt Real.pi * Real.exp (-x^2)
        - 1 / (x^2 + 1) ^ (3/2 : ℝ)) x := by
    -- rewrite the derivative using h_simp_deriv
    simpa [h_simp_deriv, one_div] using h_combined_raw

  -- Rewrite back to the original expression g z = (1 - z/√(z^2+1)) - 2 * (1 - F z)
  have h_final : HasDerivAt
      (fun z : ℝ => (1 - z / Real.sqrt (z^2 + 1)) - 2 * (1 - F z))
      (2 / Real.sqrt Real.pi * Real.exp (-x^2)
        - 1 / (x^2 + 1) ^ (3/2 : ℝ)) x := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_final'

  -- Unfold F to match the statement
  simpa [F] using h_final

open NNReal ENNReal ProbabilityTheory in
theorem refined_berry_esseen_bound_core_counterexample: ∃ (n : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/2)) (k : ℕ) (_ : 0 < k) (_ : k ≤ n),
  let hp01 : p ∈ Set.Ioo 0 1 := ⟨hp.1, lt_trans hp.2 (by norm_num)⟩;
  let σ := Real.sqrt (p * (1 - p));
  let z := (k - p * n) / (σ * Real.sqrt n);
  (1 - cdf (gaussianReal 0 1) z) >
    (binomial_tail_prob p hp01 n k + binomial_tail_prob p hp01 n (k + 1)) / 2 := by
  refine ⟨4, (1 / 4 : ℝ), ?_, 1, by norm_num, by norm_num, ?_⟩
  · -- hp : 1/4 ∈ (0,1/2)
    constructor <;> norm_num
  · -- main inequality
    -- unfold the lets in the statement
    dsimp
    -- show that the Gaussian argument z is 0
    have h_num : ((↑(1 : ℕ) : ℝ) - (1 / 4 : ℝ) * (4 : ℝ)) = (0 : ℝ) := by
      norm_num
    have h_arg :
        ((1 - (1 / 4 : ℝ) * (4 : ℝ)) /
            (Real.sqrt (1 / 4 * (1 - 1 / 4)) * Real.sqrt (4 : ℝ))) = 0 := by
      have : (1 - (1 / 4 : ℝ) * (4 : ℝ)) = (0 : ℝ) := by
        simpa using h_num
      rw [this, zero_div]
    -- simplify the left-hand side using this and the Gaussian cdf at 0
    simp [h_arg, gaussian_cdf_zero_eq_half]
    -- goal is now purely algebraic
    -- rewrite RHS binomial tail probabilities as sums (the proof argument is inferred)
    rw [binomial_tail_sum_eq (4⁻¹) _ 4 1,
        binomial_tail_sum_eq (4⁻¹) _ 4 2]
    -- expand the finite sums over Ico
    simp only [Finset.sum_Ico_succ_top (by norm_num : 1 ≤ 4),
      Finset.sum_Ico_succ_top (by norm_num : 1 ≤ 3),
      Finset.sum_Ico_succ_top (by norm_num : 1 ≤ 2),
      Finset.sum_Ico_succ_top (by norm_num : 1 ≤ 1),
      Finset.sum_Ico_succ_top (by norm_num : 2 ≤ 4),
      Finset.sum_Ico_succ_top (by norm_num : 2 ≤ 3),
      Finset.sum_Ico_succ_top (by norm_num : 2 ≤ 2),
      Finset.Ico_self, Finset.sum_empty, add_zero]
    -- now the goal is a simple inequality with binomial coefficients
    have hC2 : Nat.choose 4 2 = 6 := by decide
    have hC3 : Nat.choose 4 3 = 4 := by decide
    simp [hC2, hC3]
    norm_num

open NNReal ENNReal ProbabilityTheory in
theorem binomial_tail_2_1 (p : ℝ) (hp : p ∈ Set.Ioo 0 1) : binomial_tail_prob p hp 2 1 = 2 * p - p ^ 2 := by
  have hsum := binomial_tail_sum_eq p hp 2 1
  -- simplify the index set Finset.Ico 1 3 to {1,2}
  have hIco : Finset.Ico 1 (2 + 1) = ({1, 2} : Finset ℕ) := by
    decide
  -- rewrite the sum using this equality
  have hsum' :
      binomial_tail_prob p hp 2 1 =
        ∑ i ∈ ({1, 2} : Finset ℕ), (Nat.choose 2 i : ℝ) * p ^ i * (1 - p) ^ (2 - i) := by
    simpa [hIco] using hsum
  -- compute the finite sum over {1,2}
  have hpair :
      (∑ i ∈ ({1, 2} : Finset ℕ), (Nat.choose 2 i : ℝ) * p ^ i * (1 - p) ^ (2 - i)) =
        (Nat.choose 2 1 : ℝ) * p ^ 1 * (1 - p) ^ (2 - 1) +
        (Nat.choose 2 2 : ℝ) * p ^ 2 * (1 - p) ^ (2 - 2) := by
    -- use Finset.sum_pair for the sum over {1,2}
    have h12 : (1 : ℕ) ≠ 2 := by decide
    simpa [Finset.sum_pair, h12]
  -- combine hsum' and hpair
  have hmain : binomial_tail_prob p hp 2 1 =
      (Nat.choose 2 1 : ℝ) * p ^ 1 * (1 - p) ^ (2 - 1) +
      (Nat.choose 2 2 : ℝ) * p ^ 2 * (1 - p) ^ (2 - 2) := by
    simpa [hpair] using hsum'
  -- now simplify the explicit expressions
  have h1 :
      (Nat.choose 2 1 : ℝ) * p ^ 1 * (1 - p) ^ (2 - 1) = 2 * p * (1 - p) := by
    -- 2.choose 1 = 2, p^1 = p, (1-p)^(2-1) = (1-p)
    simp [pow_one]
  have h2 :
      (Nat.choose 2 2 : ℝ) * p ^ 2 * (1 - p) ^ (2 - 2) = p ^ 2 := by
    -- 2.choose 2 = 1, (1-p)^0 = 1
    simp [pow_two]
  -- put everything together
  have hTail : binomial_tail_prob p hp 2 1 = 2 * p * (1 - p) + p ^ 2 := by
    calc
      binomial_tail_prob p hp 2 1
          = (Nat.choose 2 1 : ℝ) * p ^ 1 * (1 - p) ^ (2 - 1) +
              (Nat.choose 2 2 : ℝ) * p ^ 2 * (1 - p) ^ (2 - 2) := hmain
      _ = 2 * p * (1 - p) + p ^ 2 := by simpa [h1, h2]
  -- final algebraic rearrangement: 2*p*(1-p) + p^2 = 2*p - p^2
  have hAlg : 2 * p * (1 - p) + p ^ 2 = 2 * p - p ^ 2 := by
    ring
  calc
    binomial_tail_prob p hp 2 1
        = 2 * p * (1 - p) + p ^ 2 := hTail
    _ = 2 * p - p ^ 2 := hAlg

open NNReal ENNReal ProbabilityTheory in
lemma sqrt_pow_two_mul (x : ℝ) (n : ℕ) (hx : 0 ≤ x) : x.sqrt ^ (2 * n) = x ^ n := by
  rw [pow_mul, Real.sq_sqrt hx]

open NNReal ENNReal ProbabilityTheory in
theorem correction_term_eq_half_prob (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (k : ℕ) :
  (1 / 2) * ((2 * k).choose k) * ((p * (1 - p)).sqrt) ^ (2 * k) =
  (1 / 2) * (binomial_tail_prob p hp (2 * k) k - binomial_tail_prob p hp (2 * k) (k + 1)) := by
  classical
  -- Set up nonnegativity facts for using the sqrt lemma
  have hp0 : 0 ≤ p := le_of_lt hp.1
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr (le_of_lt hp.2)
  have h_mul_nonneg : 0 ≤ p * (1 - p) := mul_nonneg hp0 h1p

  -- Package p as an NNReal and the corresponding bound p ≤ 1
  let p_nn : ℝ≥0 := ⟨p, le_of_lt hp.1⟩
  have hp_le : p_nn ≤ 1 := le_of_lt hp.2

  -- LHS simplification
  have h_lhs : (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * ((p * (1 - p)).sqrt) ^ (2 * k)
      = (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * (p ^ k * (1 - p) ^ k) := by
    have hs : ((p * (1 - p)).sqrt) ^ (2 * k) = (p * (1 - p)) ^ k := by
      simpa using sqrt_pow_two_mul (p * (1 - p)) k h_mul_nonneg
    simpa [hs, mul_pow]

  -- Define the binomial PMF on {0, ..., 2k} pushed forward to ℕ
  let q : PMF ℕ := (PMF.binomial p_nn hp_le (2 * k)).map (fun i => (i : ℕ))

  -- Support of q is contained in {0, ..., 2k}
  have h_supp : q.support ⊆ {x | x ≤ 2 * k} := by
    simpa [q] using binomial_pmf_map_support p_nn hp_le (2 * k)

  -- Difference of tail probabilities is the mass at k
  have h_diff :
      binomial_tail_prob p hp (2 * k) k -
        binomial_tail_prob p hp (2 * k) (k + 1)
        = (q k).toReal := by
    have h_diff' :
        ENNReal.toReal (q.toMeasure (Set.Ici k)) -
          ENNReal.toReal (q.toMeasure (Set.Ici (k + 1)))
          = (q k).toReal :=
      pmf_tail_diff_eq_mass (p := q) (n := 2 * k) (k := k) h_supp
    -- Identify binomial_tail_prob with the corresponding measure of q
    simpa [binomial_tail_prob, q, p_nn, hp_le] using h_diff'

  -- Evaluate the mass of q at k in closed form
  have h_mass : (q k).toReal = ((2 * k).choose k : ℝ) * p ^ k * (1 - p) ^ k := by
    simpa [q, p_nn] using binomial_mass_at_k_two_k (p := p_nn) (hp := hp_le) (k := k)

  -- RHS simplification using h_diff and h_mass
  have h_rhs :
      (1 / 2 : ℝ) *
          (binomial_tail_prob p hp (2 * k) k -
            binomial_tail_prob p hp (2 * k) (k + 1))
        = (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * (p ^ k * (1 - p) ^ k) := by
    calc
      (1 / 2 : ℝ) *
            (binomial_tail_prob p hp (2 * k) k -
              binomial_tail_prob p hp (2 * k) (k + 1))
          = (1 / 2 : ℝ) * (q k).toReal := by
            simpa [h_diff]
      _ = (1 / 2 : ℝ) * (((2 * k).choose k : ℝ) * p ^ k * (1 - p) ^ k) := by
            simpa [h_mass]
      _ = (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * (p ^ k * (1 - p) ^ k) := by
            ring_nf

  -- Combine the two simplifications
  calc
    (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * ((p * (1 - p)).sqrt) ^ (2 * k)
        = (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * (p ^ k * (1 - p) ^ k) := h_lhs
    _ = (1 / 2 : ℝ) *
          (binomial_tail_prob p hp (2 * k) k -
            binomial_tail_prob p hp (2 * k) (k + 1)) := by
          simpa using h_rhs.symm

open Filter Topology Set in
theorem z_strictAnti (k : ℕ) (hk : 0 < k) :
  StrictAntiOn
    (fun p : ℝ => (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p)))
    (Set.Ioo 0 (1 / 2)) := by
  -- Define the function z_fun
  let z_fun : ℝ → ℝ :=
    fun p => (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))
  -- Rewrite the goal in terms of z_fun
  change StrictAntiOn z_fun (Set.Ioo 0 (1 / 2))
  -- We will apply strictAntiOn_of_deriv_neg with D = Ioo 0 (1/2)
  set D : Set ℝ := Set.Ioo (0 : ℝ) (1 / 2) with hDdef
  have hDconvex : Convex ℝ D := by
    dsimp [D]
    simpa using (convex_Ioo (0 : ℝ) (1 / 2))
  -- interior D = D for an open interval
  have hinteriorD : interior D = D := by
    dsimp [D]
    simpa using (interior_Ioo (a := (0 : ℝ)) (b := (1 / 2)))
  -- Show continuity of z_fun on D
  have hcont : ContinuousOn z_fun D := by
    -- write z_fun as numerator / denominator
    have hnum : ContinuousOn
        (fun p : ℝ => (1 / 2 - p) * Real.sqrt (2 * (k : ℝ))) D := by
      -- (1/2 - p) is continuous, and the sqrt term is constant
      have hlin : ContinuousOn (fun p : ℝ => (1 / 2 : ℝ) - p) D :=
        (continuous_const.sub continuous_id).continuousOn
      have hconst : ContinuousOn (fun _ : ℝ => Real.sqrt (2 * (k : ℝ))) D :=
        continuous_const.continuousOn
      exact hlin.mul hconst
    have hden : ContinuousOn (fun p : ℝ => Real.sqrt (p * (1 - p))) D := by
      -- p ↦ p * (1 - p) is a polynomial, hence continuous
      have hpoly : Continuous (fun p : ℝ => p * (1 - p)) := by
        have h1 : Continuous (fun p : ℝ => p) := continuous_id
        have h2 : Continuous (fun p : ℝ => (1 : ℝ) - p) :=
          continuous_const.sub continuous_id
        simpa [mul_comm] using h1.mul h2
      -- compose with sqrt
      exact (Real.continuous_sqrt.comp hpoly).continuousOn
    -- denominator never vanishes on D
    have hden_ne : ∀ x ∈ D, Real.sqrt (x * (1 - x)) ≠ 0 := by
      intro x hx
      have hx0 : 0 < x := by
        rcases hx with ⟨hx0, hx1⟩; exact hx0
      have hx1' : x < 1 := by
        rcases hx with ⟨hx0, hx1⟩
        have : (x : ℝ) < 1 / 2 := hx1
        have hlt1 : (1 / 2 : ℝ) < 1 := by norm_num
        exact lt_trans this hlt1
      have hpos : 0 < x * (1 - x) := by
        have h1 : 0 < 1 - x := sub_pos.mpr hx1'
        have := mul_pos hx0 h1
        simpa [mul_comm] using this
      have hsqrt_pos : 0 < Real.sqrt (x * (1 - x)) := Real.sqrt_pos.mpr hpos
      exact ne_of_gt hsqrt_pos
    -- combine numerator and denominator
    have := hnum.div hden hden_ne
    -- rewrite z_fun
    intro x hx
    specialize this x hx
    simpa [z_fun] using this
  -- Derivative negative on interior D
  have hderiv_neg : ∀ x ∈ interior D, deriv z_fun x < 0 := by
    intro p hpint
    -- rewrite hpint as membership in Ioo 0 (1/2)
    have hpIoo : p ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
      have : interior D = D := hinteriorD
      have hpD : p ∈ D := by simpa [this] using hpint
      simpa [D] using hpD
    -- apply z_deriv_neg
    rcases z_deriv_neg k hk p hpIoo with ⟨hHasDerivAt, hzlt⟩
    -- Get expression for deriv
    have hderiv_eq : deriv z_fun p =
        (-Real.sqrt (2 * (k : ℝ)) / (4 * (p * (1 - p)) ^ (3 / 2 : ℝ))) := by
      -- from HasDerivAt
      have := hHasDerivAt.deriv
      -- simplify function
      simpa [z_fun] using this
    -- use this equality to show negativity
    have : deriv z_fun p < 0 := by
      simpa [hderiv_eq] using hzlt
    exact this
  -- Apply mean value theorem lemma strictAntiOn_of_deriv_neg
  have hanti_on_D : StrictAntiOn z_fun D :=
    strictAntiOn_of_deriv_neg (D := D) hDconvex hcont (by
      intro x hx
      -- x ∈ interior D
      have hx' : x ∈ interior D := hx
      simpa using hderiv_neg x hx')
  -- finally, rewrite D = Ioo 0 (1/2)
  simpa [D] using hanti_on_D

open Filter Topology Set in
theorem function_A_lower (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/8)) : function_A p ≥ Real.sqrt (1 / (4 * p)) := by
  rcases hp with ⟨hp_pos, hp_lt⟩
  rw [ge_iff_le]
  have h_pos_sqrt : 0 ≤ Real.sqrt (1 / (4 * p)) := Real.sqrt_nonneg _
  have h_pos_A : 0 ≤ function_A p := by
    unfold function_A
    apply div_nonneg
    · apply mul_nonneg
      · linarith
      · exact Real.sqrt_nonneg 2
    · apply Real.sqrt_nonneg
  rw [← sq_le_sq₀ h_pos_sqrt h_pos_A]
  rw [Real.sq_sqrt]
  · have hp : p ∈ Set.Ioo 0 (1/8) := ⟨hp_pos, hp_lt⟩
    exact function_A_sq_bound p hp
  · apply div_nonneg zero_le_one
    linarith

open Filter Topology ProbabilityTheory in
theorem gaussian_domination_helper: ∃ (C : ℝ), 0 < C ∧ (∀ᶠ p in nhdsWithin 0 (Set.Ioi 0), |ProbabilityTheory.gaussianPDFReal 0 1 (function_A p) * deriv function_A p| ≤ C * (p ^ (-(3 / 2 : ℝ)) * Real.exp (-(1 / 8) / p))) := by
  use (Real.sqrt (2 * Real.pi))⁻¹
  constructor
  · positivity
  · have : Set.Ioo 0 (1/8) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      rw [mem_nhdsWithin]
      use Set.Iio (1/8)
      constructor
      · exact isOpen_Iio
      · constructor
        · simp only [Set.mem_Iio]; norm_num
        · intro x hx; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio] at hx;
          exact ⟨hx.2, hx.1⟩
    filter_upwards [this] with p hp
    rw [gaussianPDFReal_std]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    rw [mul_comm ((Real.sqrt (2 * Real.pi))⁻¹)]
    rw [mul_assoc]
    rw [mul_comm (rexp _)]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul
      · have := deriv_function_A_bound p hp
        convert this using 1
        norm_num
      · rw [Real.exp_le_exp]
        rw [neg_div, neg_div, neg_le_neg_iff]
        have : (1 : ℝ) / 8 / p = (1 / (4 * p)) / 2 := by field_simp; ring
        rw [this]
        apply div_le_div_of_nonneg_right (function_A_sq_bound p hp)
        norm_num
      · apply Real.exp_nonneg
      · apply Real.rpow_nonneg (le_of_lt hp.1)
    · positivity

open Set Filter Topology in
theorem R_aux_crossing_unique: ∃! z0, 0 < z0 ∧ R_aux z0 = 1 ∧ (∀ z, 0 ≤ z → z ≤ z0 → 1 ≤ R_aux z) ∧ (∀ z, z0 ≤ z → R_aux z ≤ 1) := by
  classical
  -- define the peak point
  let peak : ℝ := 1 / Real.sqrt 2

  -- basic facts about peak
  have h_peak_pos : 0 < peak := by
    have h_sqrt2_pos : 0 < Real.sqrt (2 : ℝ) := by
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact Real.sqrt_pos.mpr this
    have h := one_div_pos.mpr h_sqrt2_pos
    simpa [peak] using h
  have h0_le_peak : (0 : ℝ) ≤ peak := le_of_lt h_peak_pos

  -- continuity of L_aux
  have hL_cont : Continuous L_aux := by
    unfold L_aux
    -- continuity of constant term
    have h_const : Continuous fun _ : ℝ => Real.log (2 / Real.sqrt Real.pi) :=
      continuous_const
    -- continuity of z^2
    have h_z2 : Continuous fun z : ℝ => z ^ 2 := by
      simpa [pow_two] using (continuous_id.mul continuous_id :
        Continuous fun z : ℝ => z * z)
    -- continuity of z^2 + 1
    have h_z2_add : Continuous fun z : ℝ => z ^ 2 + 1 :=
      h_z2.add continuous_const
    -- continuity of log (z^2 + 1)
    have h_log_z2 : Continuous fun z : ℝ => Real.log (z ^ 2 + 1) := by
      refine Continuous.log h_z2_add ?h_ne
      intro x
      have hx_pos : 0 < x ^ 2 + 1 := by
        have hx2_nonneg : 0 ≤ x ^ 2 := by
          have := sq_nonneg x
          simpa [pow_two] using this
        have h1 : (0 : ℝ) < 1 := by norm_num
        have hx1 : 0 < x ^ 2 + 1 := by linarith
        exact hx1
      exact ne_of_gt hx_pos
    -- first part: log const - z^2
    have h_term1 : Continuous fun z : ℝ =>
        Real.log (2 / Real.sqrt Real.pi) - z ^ 2 :=
      h_const.sub h_z2
    -- second part: (3/2) * log(z^2 + 1)
    have h_term2 : Continuous fun z : ℝ =>
        (3 / 2 : ℝ) * Real.log (z ^ 2 + 1) :=
      continuous_const.mul h_log_z2
    -- combine
    have h_all : Continuous fun z : ℝ =>
        (Real.log (2 / Real.sqrt Real.pi) - z ^ 2) +
          (3 / 2 : ℝ) * Real.log (z ^ 2 + 1) :=
      h_term1.add h_term2
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_all

  -- monotonicity of L_aux from the lemma
  have h_strict_mono : StrictMonoOn L_aux (Icc 0 peak) := by
    simpa [peak] using (L_aux_shape).1
  have h_strict_anti : StrictAntiOn L_aux (Ici peak) := by
    simpa [peak] using (L_aux_shape).2

  -- L_aux(0) > 0
  have h_L0_pos : 0 < L_aux 0 := by
    have h_log : L_aux 0 = Real.log (R_aux 0) := R_aux_log_eq 0
    have hR0_nonneg : 0 ≤ R_aux 0 := le_of_lt (R_aux_pos 0)
    have h_log_pos : 0 < Real.log (R_aux 0) := by
      have h1 : 1 < R_aux 0 := R_aux_zero_gt_one
      have := (Real.log_pos_iff hR0_nonneg).2 h1
      exact this
    simpa [h_log] using h_log_pos

  -- deduce L_aux(peak) > 0 using strict monotonicity on [0, peak]
  have h_L_peak_pos : 0 < L_aux peak := by
    have h0_mem : (0 : ℝ) ∈ Icc 0 peak := by exact ⟨le_rfl, h0_le_peak⟩
    have hpeak_mem : peak ∈ Icc 0 peak := by exact ⟨h0_le_peak, le_rfl⟩
    have h_lt : (0 : ℝ) < peak := h_peak_pos
    have h_lt' : L_aux 0 < L_aux peak := h_strict_mono h0_mem hpeak_mem h_lt
    exact lt_trans h_L0_pos h_lt'

  -- from this, get R_aux(peak) > 1
  have h_R_peak_gt1 : 1 < R_aux peak := by
    have h_log_peak_pos : 0 < Real.log (R_aux peak) := by
      have : 0 < L_aux peak := h_L_peak_pos
      -- rewrite using log equality
      simpa [R_aux_log_eq peak] using this
    have hR_peak_nonneg : 0 ≤ R_aux peak := le_of_lt (R_aux_pos peak)
    exact (Real.log_pos_iff hR_peak_nonneg).1 h_log_peak_pos

  -- R_aux tends to 0 at +∞, hence eventually < 1
  have h_event_lt1 : ∀ᶠ z in atTop, R_aux z < 1 := by
    have hnhds : (Set.Iio (1 : ℝ)) ∈ nhds (0 : ℝ) := by
      have h0 : (0 : ℝ) < 1 := by norm_num
      exact Iio_mem_nhds h0
    exact (R_aux_limit_atTop.eventually hnhds)

  obtain ⟨b, hb⟩ := (Filter.eventually_atTop.1 h_event_lt1)
  -- hb : ∀ z ≥ b, R_aux z < 1

  -- choose c ≥ max b peak
  let c : ℝ := max b peak
  have hbc : b ≤ c := le_max_left _ _
  have h_peak_le_c : peak ≤ c := le_max_right _ _
  have h_Rc_lt1 : R_aux c < 1 := hb c hbc

  -- convert this to L_aux c < 0
  have h_Lc_neg : L_aux c < 0 := by
    have hlog_neg : Real.log (R_aux c) < 0 :=
      Real.log_neg (R_aux_pos c) h_Rc_lt1
    have h_eq : L_aux c = Real.log (R_aux c) := R_aux_log_eq c
    simpa [h_eq] using hlog_neg

  -- continuity of L_aux on [peak, c]
  have hL_cont_on : ContinuousOn L_aux (Icc peak c) :=
    hL_cont.continuousOn

  -- use IVT (decreasing version) to find z0 with L_aux z0 = 0 between peak and c
  have h_between : (0 : ℝ) ∈ Icc (L_aux c) (L_aux peak) := by
    exact ⟨le_of_lt h_Lc_neg, le_of_lt h_L_peak_pos⟩

  have h_IVT :=
    intermediate_value_Icc' (a := peak) (b := c) (f := L_aux)
      h_peak_le_c hL_cont_on
  have h_image := h_IVT h_between
  rcases h_image with ⟨z0, hz0_mem, hz0_eq⟩

  have h_peak_le_z0 : peak ≤ z0 := hz0_mem.1
  have hz0_le_c : z0 ≤ c := hz0_mem.2
  have hz0_pos : 0 < z0 := lt_of_lt_of_le h_peak_pos h_peak_le_z0

  -- show R_aux z0 = 1
  have h_Rz0_one : R_aux z0 = 1 := by
    -- from hz0_eq : L_aux z0 = 0 and log equality
    have hlogR0_zero : Real.log (R_aux z0) = 0 := by
      have h_eq : L_aux z0 = Real.log (R_aux z0) := R_aux_log_eq z0
      have h0 : (0 : ℝ) = Real.log (R_aux z0) := by
        exact hz0_eq.symm.trans h_eq
      simpa using h0.symm
    have hexp := congrArg Real.exp hlogR0_zero
    simpa [Real.exp_log, R_aux_pos z0] using hexp

  -- antitone / monotone versions on the regions
  have h_antitone : AntitoneOn L_aux (Ici peak) :=
    h_strict_anti.antitoneOn
  have h_monotone : MonotoneOn L_aux (Icc 0 peak) :=
    h_strict_mono.monotoneOn

  -- L_aux is ≥ 0 on [0, z0]
  have h_L_nonneg_left : ∀ {z}, 0 ≤ z → z ≤ z0 → 0 ≤ L_aux z := by
    intro z hz_nonneg hz_le
    by_cases hz_le_peak : z ≤ peak
    · -- case z ≤ peak : use monotonicity from 0
      have h0_mem : (0 : ℝ) ∈ Icc (0 : ℝ) peak := ⟨le_rfl, h0_le_peak⟩
      have hz_mem : z ∈ Icc (0 : ℝ) peak := ⟨hz_nonneg, hz_le_peak⟩
      have hmono := h_monotone h0_mem hz_mem hz_nonneg
      have hL0_nonneg : (0 : ℝ) ≤ L_aux 0 := le_of_lt h_L0_pos
      exact le_trans hL0_nonneg hmono
    · -- case peak ≤ z ≤ z0 : use antitonicity and value at z0
      have h_peak_le_z : peak ≤ z := le_of_not_ge hz_le_peak
      have hz_in : z ∈ Ici peak := h_peak_le_z
      have hz0_in : z0 ∈ Ici peak := h_peak_le_z0
      have hanti := h_antitone hz_in hz0_in hz_le
      -- hanti : L_aux z0 ≤ L_aux z
      have hz0_zero : L_aux z0 = 0 := hz0_eq
      have : 0 ≤ L_aux z := by
        have := hanti
        simpa [hz0_zero] using this
      exact this

  -- L_aux is ≤ 0 on [z0, ∞)
  have h_L_nonpos_right : ∀ {z}, z0 ≤ z → L_aux z ≤ 0 := by
    intro z hz0_le_z
    have hz0_in : z0 ∈ Ici peak := h_peak_le_z0
    have hz_in : z ∈ Ici peak := le_trans h_peak_le_z0 hz0_le_z
    have hanti := h_antitone hz0_in hz_in hz0_le_z
    -- hanti : L_aux z ≤ L_aux z0
    have hz0_zero : L_aux z0 = 0 := hz0_eq
    have : L_aux z ≤ 0 := by
      have := hanti
      simpa [hz0_zero] using this
    exact this

  -- Now show that z0 satisfies the required properties
  refine ⟨z0, ?hexists, ?huniq⟩

  -- existence part
  · refine And.intro hz0_pos ?hrest
    -- collect equalities and inequalities for R_aux via log
    have h_left : ∀ z, 0 ≤ z → z ≤ z0 → 1 ≤ R_aux z := by
      intro z hz_nonneg hz_le
      have hL_nonneg : 0 ≤ L_aux z := h_L_nonneg_left hz_nonneg hz_le
      have h_log_nonneg : 0 ≤ Real.log (R_aux z) := by
        simpa [R_aux_log_eq z] using hL_nonneg
      have hR_pos : 0 < R_aux z := R_aux_pos z
      have h := (Real.log_nonneg_iff hR_pos).1 h_log_nonneg
      exact h
    have h_right : ∀ z, z0 ≤ z → R_aux z ≤ 1 := by
      intro z hz0_le_z
      have hL_nonpos : L_aux z ≤ 0 := h_L_nonpos_right hz0_le_z
      have h_log_nonpos : Real.log (R_aux z) ≤ 0 := by
        simpa [R_aux_log_eq z] using hL_nonpos
      have hR_nonneg : 0 ≤ R_aux z := le_of_lt (R_aux_pos z)
      have h := (Real.log_nonpos_iff hR_nonneg).1 h_log_nonpos
      exact h
    exact ⟨h_Rz0_one, h_left, h_right⟩

  -- uniqueness part
  · intro z hz_prop
    rcases hz_prop with ⟨hz_pos, hz_eq1, hz_left, hz_right⟩
    -- first, show L_aux z = 0
    have hLz_zero : L_aux z = 0 := by
      simpa [R_aux_log_eq z, hz_eq1] using (R_aux_log_eq z)
    -- show peak ≤ z, otherwise we contradict R_aux peak > 1
    have h_peak_le_z : peak ≤ z := by
      by_contra hlt
      have hz_le_peak : z ≤ peak := le_of_not_ge hlt
      have hR_peak_le1 : R_aux peak ≤ 1 := hz_right peak hz_le_peak
      exact (not_le_of_gt h_R_peak_gt1) hR_peak_le1
    -- now use strict anti-monotonicity on [peak, ∞)
    have hz_in : z ∈ Ici peak := h_peak_le_z
    have hz0_in : z0 ∈ Ici peak := h_peak_le_z0
    have hz0_zero : L_aux z0 = 0 := hz0_eq
    -- if z ≠ z0, derive a contradiction
    by_contra hne
    have hlt_or_gt : z < z0 ∨ z0 < z := lt_or_gt_of_ne hne
    cases hlt_or_gt with
    | inl hz_lt_z0 =>
        have hlt : L_aux z > L_aux z0 := h_strict_anti hz_in hz0_in hz_lt_z0
        have : (0 : ℝ) > 0 := by simpa [hLz_zero, hz0_zero] using hlt
        exact lt_irrefl _ this
    | inr hz0_lt_z =>
        have hlt : L_aux z0 > L_aux z := h_strict_anti hz0_in hz_in hz0_lt_z
        have : (0 : ℝ) > 0 := by simpa [hLz_zero, hz0_zero] using hlt
        exact lt_irrefl _ this

open Filter Topology Set in
theorem psi_limit_zero (k : ℕ) (hk : 0 < k) : Filter.Tendsto (psi_def k) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  classical
  -- We rewrite the statement using the right-sided neighborhood notation.
  have hnhds : nhdsWithin 0 (Set.Ioi (0 : ℝ)) = 𝓝[>] (0 : ℝ) := rfl

  -- Constants in the linear-minus-log expression.
  let a : ℝ := k
  let b : ℝ := k + 1 / 2
  have ha : 0 < a := by
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    simpa [a] using hk'
  have hb : 0 < b := by
    have hk' : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    have hhalf : 0 < (1 : ℝ) / 2 := by norm_num
    have : 0 < (k : ℝ) + 1 / 2 := by exact add_pos_of_nonneg_of_pos hk' hhalf
    simpa [b] using this

  -- Auxiliary functions in terms of `p`.
  let s : ℝ → ℝ := fun p => p * (1 - p)
  let t : ℝ → ℝ := fun p => 1 / (4 * s p)

  -- Step 1: `s p → 0` as `p → 0⁺`.
  have hs_tendsto : Tendsto s (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    -- Use continuity of `p ↦ p * (1 - p)` and restriction of the filter.
    have hs_cont : Continuous fun p : ℝ => p * (1 - p) := by
      have h1 : Continuous fun p : ℝ => p := continuous_id
      have h2 : Continuous fun p : ℝ => 1 - p := continuous_const.sub continuous_id
      simpa [s, mul_comm, mul_left_comm, mul_assoc] using h1.mul h2
    have hs_tendsto_nhds : Tendsto s (𝓝 (0 : ℝ)) (𝓝 (s 0)) := (hs_cont.tendsto 0)
    have : Tendsto s (𝓝 (0 : ℝ)) (𝓝 0) := by simpa [s] using hs_tendsto_nhds
    exact this.mono_left nhdsWithin_le_nhds

  -- Step 2: `s p > 0` eventually on `𝓝[>] 0`.
  have hs_pos : (∀ᶠ p in 𝓝[>] (0 : ℝ), 0 < s p) := by
    -- On `Ioi 0`, `p` is positive; and near `0` we can ensure `p < 1`.
    have h_pos_p : (∀ᶠ p in 𝓝[>] (0 : ℝ), 0 < p) := by
      refine Filter.eventually_of_mem (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)) ?_
      intro p hp; exact hp
    have h_tendsto_id : Tendsto (fun p : ℝ => p) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_id : Tendsto (fun p : ℝ => p) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds
    have h_lt_one : (∀ᶠ p in 𝓝[>] (0 : ℝ), p < 1) := by
      -- By `p → 0`, for any `u > 0` we eventually have `p < u`; take `u = 1`.
      have h0 : (0 : ℝ) < 1 := by norm_num
      -- `eventually_lt_const` expects `v < u` and `Tendsto f l (𝓝 v)`.
      have := (Filter.Tendsto.eventually_lt_const (l := 𝓝[>] (0 : ℝ))
        (f := fun p : ℝ => p) (u := (1 : ℝ)) (v := (0 : ℝ)) h0 h_tendsto_id)
      simpa using this
    have h_pos_and_lt : (∀ᶠ p in 𝓝[>] (0 : ℝ), 0 < p ∧ p < 1) := h_pos_p.and h_lt_one
    refine h_pos_and_lt.mono ?_
    intro p hp
    have hp_pos : 0 < p := hp.1
    have hp_lt_one : p < 1 := hp.2
    have h1 : 0 < 1 - p := sub_pos.mpr hp_lt_one
    have : 0 < p * (1 - p) := mul_pos hp_pos h1
    simpa [s] using this

  -- Step 3: `t p → +∞` as `p → 0⁺`.
  have ht_atTop : Tendsto t (𝓝[>] (0 : ℝ)) atTop := by
    -- First, show that `s p → 0⁺`, i.e., to `0` with positive values.
    have hs_to_right : Tendsto s (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      -- use the characterization via `tendsto_nhdsWithin_iff`
      refine (tendsto_nhdsWithin_iff.2 ?_)
      refine And.intro hs_tendsto ?_
      -- eventual positivity of `s p` gives membership in `Ioi 0`.
      simpa [Set.Ioi] using hs_pos
    -- Now apply the inversion lemma.
    have ht_inv : Tendsto (fun p : ℝ => (s p)⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      (Filter.Tendsto.inv_tendsto_nhdsGT_zero (f := s) hs_to_right)
    -- Finally, `t p = (1 / 4) * (s p)⁻¹`, so multiply by a positive constant.
    have ht_eq : t = fun p => (1 / 4 : ℝ) * (s p)⁻¹ := by
      funext p
      -- `one_div_mul_one_div` says `(1/4) * (1/s) = 1/(4*s)`.
      have h := (one_div_mul_one_div (a := (4 : ℝ)) (b := s p))
      -- rewrite both sides to match `t` and RHS.
      simpa [t, s, one_div, mul_comm, mul_left_comm, mul_assoc] using h.symm
    -- Use the fact that multiplying by a positive constant preserves `atTop`.
    have hmul : Tendsto (fun p : ℝ => (1 / 4 : ℝ) * (s p)⁻¹) (𝓝[>] (0 : ℝ)) atTop := by
      have hconst : (0 : ℝ) < 1 / 4 := by norm_num
      exact (Filter.Tendsto.const_mul_atTop' (l := 𝓝[>] (0 : ℝ))
        (f := fun p => (s p)⁻¹) (r := (1 / 4 : ℝ)) hconst ht_inv)
    simpa [ht_eq] using hmul

  -- Step 4: rewrite `psi_def` in terms of `t` and compare with the linear-minus-log expression.
  have h_eq :
      (fun p : ℝ => a * t p - b * Real.log (t p) - (k + (k + 1 / 2 : ℝ) * Real.log 4))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (psi_def k) := by
    -- We work on the set where `s p > 0`, so that all logarithms are well-behaved.
    refine hs_pos.mono ?_
    intro p hp_pos
    have hs_ne : s p ≠ 0 := ne_of_gt hp_pos
    have h4_ne : (4 : ℝ) ≠ 0 := by norm_num
    -- express `log (t p)` in terms of `log (s p)`.
    have hlog_t : Real.log (t p) = - (Real.log 4 + Real.log (s p)) := by
      calc
        Real.log (t p)
            = Real.log (1 / (4 * s p)) := by simpa [t]
        _ = Real.log ((4 * s p)⁻¹) := by
              simp [one_div]
        _ = - Real.log (4 * s p) := by
              simpa using (Real.log_inv (x := 4 * s p))
        _ = - (Real.log 4 + Real.log (s p)) := by
              have hmul : Real.log (4 * s p) = Real.log 4 + Real.log (s p) := by
                simpa [mul_comm] using
                  (Real.log_mul (x := 4) (y := s p) h4_ne hs_ne)
              simpa [hmul, neg_add, add_comm, add_left_comm, add_assoc]
    -- hence `log (s p)` in terms of `log (t p)`.
    have hlog_s : Real.log (s p) = - Real.log 4 - Real.log (t p) := by
      -- from `hlog_t` we have `log t = - (log 4 + log s)`; rearrange.
      have h1 := congrArg (fun x => -x) hlog_t
      -- `h1 : -log (t p) = - (-(Real.log 4 + Real.log (s p))) = Real.log 4 + Real.log (s p)`.
      have h2 : - Real.log (t p) = Real.log 4 + Real.log (s p) := by
        simpa [neg_add, add_comm, add_left_comm, add_assoc] using h1
      -- subtract `log 4` from both sides.
      have h3 := congrArg (fun x => x - Real.log 4) h2
      have h4 : - Real.log (t p) - Real.log 4 = Real.log (s p) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h3
      -- rearrange to desired form.
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h4.symm
    -- Now rewrite `psi_def`.
    have hpsi1 : psi_def k p =
        (k : ℝ) / (4 * s p) - k + (k + 1 / 2 : ℝ) * (- Real.log 4 - Real.log (t p)) := by
      simp [psi_def, s, hlog_s]
    have hpsi2 : psi_def k p =
        a * t p - b * Real.log (t p) - (k + (k + 1 / 2 : ℝ) * Real.log 4) := by
      -- First, turn the division into multiplication by `t p` and expand.
      have hlin : (k : ℝ) / (4 * s p) = a * t p := by
        simp [a, t, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      -- Now compute using algebraic manipulations.
      have :
          (k : ℝ) / (4 * s p) - k + (k + 1 / 2 : ℝ) * (- Real.log 4 - Real.log (t p))
            = a * t p - b * Real.log (t p) - (k + (k + 1 / 2 : ℝ) * Real.log 4) := by
        calc
          (k : ℝ) / (4 * s p) - k + (k + 1 / 2 : ℝ) * (- Real.log 4 - Real.log (t p))
              = a * t p - k + b * (- Real.log 4 - Real.log (t p)) := by
                simp [hlin, a, b]
          _ = a * t p - k - b * Real.log 4 - b * Real.log (t p) := by
                ring
          _ = a * t p - b * Real.log (t p) - (k + b * Real.log 4) := by
                ring
          _ = a * t p - b * Real.log (t p) - (k + (k + 1 / 2 : ℝ) * Real.log 4) := by
                simp [b]
      exact hpsi1.trans this
    -- This is the equality we need, but note the orientation for `=ᶠ`.
    -- We want the "linear minus log" expression on the left.
    have : a * t p - b * Real.log (t p) - (k + (k + 1 / 2 : ℝ) * Real.log 4)
        = psi_def k p := by simpa [hpsi2]
    exact this

  -- Step 5: apply the general growth lemma and compose with `t`.
  have h_comp :
      Tendsto (fun p : ℝ => a * t p - b * Real.log (t p)) (𝓝[>] (0 : ℝ)) atTop := by
    have h_linlog : Tendsto (fun u : ℝ => a * u - b * Real.log u) atTop atTop :=
      tendsto_linear_sub_log_atTop_v2 a b ha hb
    exact h_linlog.comp ht_atTop

  -- Shift by the constant `k + (k + 1 / 2) * log 4`.
  have h_shift : Tendsto
      (fun p : ℝ => a * t p - b * Real.log (t p) - (k + (k + 1 / 2 : ℝ) * Real.log 4))
      (𝓝[>] (0 : ℝ)) atTop := by
    -- use that adding/subtracting a constant preserves divergence to `+∞`.
    have h_add_const :=
      (Filter.tendsto_atTop_add_const_right
        (C := -(k + (k + 1 / 2 : ℝ) * Real.log 4))
        (hf := h_comp))
    -- `tendsto_atTop_add_const_right` gives
    -- `Tendsto (fun p => (a * t p - b * log (t p)) + (-(k + (k+1/2)*log 4))) _ atTop`.
    -- We rewrite this in a more convenient form.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_add_const

  -- Now use eventual equality to transfer the limit to `psi_def k`.
  have hpsi : Tendsto (psi_def k) (𝓝[>] (0 : ℝ)) atTop :=
    (Filter.Tendsto.congr' h_eq h_shift)

  -- Finally, rewrite the filter back to the original expression.
  simpa [hnhds] using hpsi

open Filter Topology Set in
theorem psi_at_half (k : ℕ) : let s_half := (1 / 2 : ℝ) * (1 - 1 / 2); (k : ℝ) / (4 * s_half) - k + (k + 1/2 : ℝ) * Real.log s_half = -(k + 1 / 2 : ℝ) * Real.log 4 := by
  intro s_half
  simp only [s_half]
  norm_num
  have h : Real.log (1 / 4) = -Real.log 4 := by
    rw [← Real.log_inv]
    norm_num
  rw [h]
  ring

open Filter Topology Set in
theorem psi_deriv (k : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/2)) : deriv (fun x => (k : ℝ) / (4 * x * (1 - x)) - k + (k + 1/2 : ℝ) * Real.log (x * (1 - x))) p = ((1 - 2 * p) / (p * (1 - p))) * (k + 1/2 - k / (4 * p * (1 - p))) := by
  classical
  have hpos : 0 < p := hp.1
  have hlt_half : p < (1 / 2 : ℝ) := hp.2
  have hlt_one : p < (1 : ℝ) := lt_trans hlt_half (by norm_num)
  have hpos1 : 0 < 1 - p := sub_pos.mpr hlt_one
  have hne0 : (p : ℝ) ≠ 0 := ne_of_gt hpos
  have hne1 : (1 - p) ≠ 0 := ne_of_gt hpos1
  have hne_s : p * (1 - p) ≠ 0 := mul_ne_zero hne0 hne1

  -- define sfun(x) = x * (1 - x)
  let sfun : ℝ → ℝ := fun x => x * (1 - x)

  -- derivative of sfun at p: 1 - 2p
  have hHas_s : HasDerivAt sfun (1 - 2 * p) p := by
    have hx : HasDerivAt (fun x : ℝ => x) 1 p := by
      simpa using (hasDerivAt_id (x := p))
    have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * p) p := by
      simpa [two_mul, mul_comm] using (hasDerivAt_pow (n := 2) (x := p))
    have hdiff : HasDerivAt (fun x : ℝ => x - x ^ 2) (1 - 2 * p) p := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        hx.sub hx2
    have h_eq : sfun = fun x : ℝ => x - x ^ 2 := by
      funext x; ring
    simpa [sfun, h_eq] using hdiff

  -- derivative of log(sfun x)
  have hHas_log_inner :
      HasDerivAt (fun x : ℝ => Real.log (sfun x))
        ((1 - 2 * p) / (sfun p)) p := by
    have hs_ne : sfun p ≠ 0 := by
      simpa [sfun, mul_comm, mul_left_comm, mul_assoc] using hne_s
    have h := hHas_s.log hs_ne
    simpa [sfun] using h

  -- derivative of (k + 1/2) * log(sfun x)
  have hHas_g3 :
      HasDerivAt (fun x : ℝ => (k + 1 / 2 : ℝ) * Real.log (sfun x))
        ((k + 1 / 2 : ℝ) * ((1 - 2 * p) / (sfun p))) p := by
    simpa using hHas_log_inner.const_mul (k + 1 / 2 : ℝ)

  -- derivative of (sfun x)^{-1}
  have hHas_inv :
      HasDerivAt (fun x : ℝ => (sfun x)⁻¹)
        (-(1 - 2 * p) / (sfun p) ^ 2) p := by
    have hs_ne : sfun p ≠ 0 := by
      simpa [sfun, mul_comm, mul_left_comm, mul_assoc] using hne_s
    have h := hHas_s.fun_inv hs_ne
    simpa using h

  -- derivative of ((k:ℝ)/4) * (sfun x)^{-1}
  have hHas_g1 :
      HasDerivAt (fun x : ℝ => ((k : ℝ) / 4) * (sfun x)⁻¹)
        (((k : ℝ) / 4) * (-(1 - 2 * p) / (sfun p) ^ 2)) p := by
    simpa using hHas_inv.const_mul ((k : ℝ) / 4)

  -- derivative of sum g1 + g3
  have hHas_sum :
      HasDerivAt
        (fun x : ℝ =>
          ((k : ℝ) / 4) * (sfun x)⁻¹ +
            (k + 1 / 2 : ℝ) * Real.log (sfun x))
        (((k : ℝ) / 4) * (-(1 - 2 * p) / (sfun p) ^ 2)
          + (k + 1 / 2 : ℝ) * ((1 - 2 * p) / (sfun p))) p := by
    simpa [add_comm, add_left_comm, add_assoc] using
      hHas_g1.add hHas_g3

  -- use `deriv` for the sum
  have hderiv_sum :
      deriv
        (fun x : ℝ =>
          ((k : ℝ) / 4) * (sfun x)⁻¹ +
            (k + 1 / 2 : ℝ) * Real.log (sfun x)) p
      = ((k : ℝ) / 4) * (-(1 - 2 * p) / (sfun p) ^ 2)
        + (k + 1 / 2 : ℝ) * ((1 - 2 * p) / (sfun p)) :=
    hHas_sum.deriv

  -- rewrite this sum in terms of x*(1-x)
  let f1 : ℝ → ℝ := fun x : ℝ =>
    (k : ℝ) / (4 * x * (1 - x)) +
      (k + 1 / 2 : ℝ) * Real.log (x * (1 - x))

  have hderiv_f1 :
      deriv f1 p
      = ((k : ℝ) / 4) * (-(1 - 2 * p) / (sfun p) ^ 2)
        + (k + 1 / 2 : ℝ) * ((1 - 2 * p) / (sfun p)) := by
    -- rewrite function inside deriv using simplification
    simpa [f1, sfun, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using hderiv_sum

  -- full function including the constant term -k
  let f : ℝ → ℝ := fun x : ℝ =>
    (k : ℝ) / (4 * x * (1 - x)) - k +
      (k + 1 / 2 : ℝ) * Real.log (x * (1 - x))

  -- derivative of f equals derivative of f1 (constant disappears)
  have hrel :
      deriv f p = deriv f1 p := by
    simpa [f, f1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (deriv_add_const (f := f1) (x := p) (c := -(k : ℝ)))

  have hderiv_f :
      deriv f p
      = ((k : ℝ) / 4) * (-(1 - 2 * p) / (sfun p) ^ 2)
        + (k + 1 / 2 : ℝ) * ((1 - 2 * p) / (sfun p)) := by
    calc
      deriv f p = deriv f1 p := hrel
      _ = ((k : ℝ) / 4) * (-(1 - 2 * p) / (sfun p) ^ 2)
          + (k + 1 / 2 : ℝ) * ((1 - 2 * p) / (sfun p)) := hderiv_f1

  -- rewrite sfun p to p * (1 - p) in the derivative expression
  have hderiv_simp :
      deriv f p
      = ((k : ℝ) / 4) * ((2 * p - 1) / (p * (1 - p)) ^ 2)
        + (k + 1 / 2 : ℝ) * ((1 - 2 * p) / (p * (1 - p))) := by
    -- note: simp will rewrite `-(1 - 2 * p)` as `2 * p - 1`
    simpa [sfun, mul_comm, mul_left_comm, mul_assoc] using hderiv_f

  -- algebraic simplification on the right-hand side
  have halg :
      ((k : ℝ) / 4) * ((2 * p - 1) / (p * (1 - p)) ^ 2)
        + (k + 1 / 2 : ℝ) * ((1 - 2 * p) / (p * (1 - p)))
      = ((1 - 2 * p) / (p * (1 - p))) *
          ((k + 1 / 2 : ℝ) - (k : ℝ) / (4 * p * (1 - p))) := by
    have hne_s' : (p * (1 - p)) ≠ 0 := hne_s
    field_simp [hne_s']
    ring

  -- final step: combine derivative computation with algebraic identity
  -- and rewrite `f` back to the original function
  have hfinal :
      deriv f p
      = ((1 - 2 * p) / (p * (1 - p))) *
          ((k + 1 / 2 : ℝ) - (k : ℝ) / (4 * p * (1 - p))) := by
    calc
      deriv f p
          = ((k : ℝ) / 4) * ((2 * p - 1) / (p * (1 - p)) ^ 2)
              + (k + 1 / 2 : ℝ) * ((1 - 2 * p) / (p * (1 - p))) := hderiv_simp
      _ = ((1 - 2 * p) / (p * (1 - p))) *
            ((k + 1 / 2 : ℝ) - (k : ℝ) / (4 * p * (1 - p))) := halg

  -- Conclude with the original function
  simpa [f] using hfinal

open ProbabilityTheory NNReal ENNReal Set in
theorem binomial_tail_eq_integral (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) : binomial_tail_prob p hp n k = binomial_tail_integral n k p := by
  classical
  -- We proceed by cases on whether k < n or k = n.
  have hk1 : 1 ≤ k := Nat.succ_le_of_lt hk
  by_cases hkn_lt : k < n
  · ----------------------------------------------------------------------
    -- Interior case: 1 ≤ k < n
    ----------------------------------------------------------------------
    have hn1 : 1 ≤ n := le_trans hk1 (Nat.le_of_lt hkn_lt)

    -- Define F as the binomial tail sum (as a function of x), and f as the
    -- telescoping term that will be its derivative.
    let F : ℝ → ℝ := fun x => ∑ i ∈ Finset.Ico k (n + 1), binomial_term n i x
    let f : ℝ → ℝ := fun x => telescoping_term n (k - 1) x

    -- Derivative of F is f: differentiate termwise and use the telescoping identity.
    have h_deriv : ∀ x, HasDerivAt F (f x) x := by
      intro x
      -- Derivative of the finite sum using HasDerivAt.fun_sum.
      have hsum_deriv' :
          HasDerivAt (fun x => ∑ i ∈ Finset.Ico k (n + 1), binomial_term n i x)
            (∑ i ∈ Finset.Ico k (n + 1),
              (telescoping_term n (i - 1) x - telescoping_term n i x)) x := by
        refine HasDerivAt.fun_sum (u := Finset.Ico k (n + 1))
          (A := fun i x => binomial_term n i x)
          (A' := fun i => telescoping_term n (i - 1) x - telescoping_term n i x)
          (x := x) ?_
        intro i hi
        -- bounds 1 ≤ i ≤ n for indices in Ico k (n+1)
        have hi_bounds : k ≤ i ∧ i < n + 1 := by
          simpa [Finset.mem_Ico] using hi
        have hi_min : 1 ≤ i := le_trans hk1 hi_bounds.1
        have hi_max : i ≤ n := Nat.le_of_lt_succ hi_bounds.2
        -- apply the given derivative lemma
        simpa using binomial_term_deriv (n := n) (i := i) (x := x) hi_min hi_max
      -- Collapse the derivative sum using the telescoping identity.
      have htel_sum :
          (∑ i ∈ Finset.Ico k (n + 1),
              (telescoping_term n (i - 1) x - telescoping_term n i x))
            = telescoping_term n (k - 1) x := by
        simpa using telescoping_sum_identity (n := n) (k := k) (x := x)
          (hk := hk1) (hkn := hkn_lt)
      have hsum_deriv :
          HasDerivAt (fun x => ∑ i ∈ Finset.Ico k (n + 1), binomial_term n i x)
            (telescoping_term n (k - 1) x) x := by
        simpa [htel_sum] using hsum_deriv'
      -- This is exactly HasDerivAt F (f x) x.
      simpa [F, f] using hsum_deriv

    -- F(0) = 0, since each term in the sum has factor 0^i with i ≥ 1.
    have hF0 : F 0 = 0 := by
      dsimp [F]
      have hzero : ∀ i ∈ Finset.Ico k (n + 1), binomial_term n i 0 = 0 := by
        intro i hi
        have hi_bounds : k ≤ i ∧ i < n + 1 := by
          simpa [Finset.mem_Ico] using hi
        have hi_pos : 0 < i := lt_of_lt_of_le hk hi_bounds.1
        -- simplify binomial_term n i 0 via 0^i = 0 for i ≥ 1
        simp [binomial_term, hi_pos.ne']
      refine Finset.sum_eq_zero ?_
      intro i hi
      exact hzero i hi

    -- Fundamental theorem of calculus: integrate f to get F p - F 0.
    have h_ftc : ∫ t in (0)..p, f t = F p - F 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
      · intro x hx; exact h_deriv x
      · have hcont : Continuous f := by
          simpa [f] using continuous_telescoping_term n (k - 1)
        exact hcont.intervalIntegrable 0 p

    -- Express the probability side as F p using the binomial tail sum lemma.
    have h_prob : binomial_tail_prob p hp n k = F p := by
      have h_sum :
        binomial_tail_prob p hp n k =
          ∑ i ∈ Finset.Ico k (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) :=
        binomial_tail_sum_eq p hp n k
      -- Rewrite the sum in terms of binomial_term.
      simpa [F, binomial_term] using h_sum

    -- Combinatorial identity relating coefficients.
    have h_coeff : (n.choose k : ℝ) * k = n * (n - 1).choose (k - 1) := by
      simpa using combinatorial_identity_1 (n := n) (i := k) (hi := hk1) (hn := hn1)

    -- Show that f is exactly the Beta integrand up to the factor (n.choose k)*k.
    have h_f_eq : ∀ t, f t = ((n.choose k : ℝ) * k) * (t^(k-1) * (1-t)^(n-k)) := by
      intro t
      dsimp [f, telescoping_term]
      rw [← h_coeff]
      have pow_eq : n - 1 - (k - 1) = n - k := by
        omega
      simp [pow_eq, mul_left_comm, mul_assoc]

    -- Use FTC to represent F p as the integral of the Beta integrand.
    have h_eq : F p = binomial_tail_integral n k p := by
      -- From FTC: ∫_0^p f = F p - F 0, but F 0 = 0.
      have h_ftc' : ∫ t in (0)..p, f t = F p := by
        have := h_ftc
        simpa [hF0, sub_zero] using this
      -- Replace f by the explicit integrand and factor out the constant.
      have h_int_f : ∫ t in (0)..p, f t =
          (n.choose k : ℝ) * k * ∫ t in (0)..p, t^(k-1) * (1-t)^(n-k) := by
        -- Congruence of integrals via pointwise equality of integrands.
        have hcongr :
            ∫ t in (0)..p, f t
              = ∫ t in (0)..p,
                  ((n.choose k : ℝ) * k) * (t^(k-1) * (1-t)^(n-k)) := by
          refine intervalIntegral.integral_congr ?_
          intro t ht; simp [h_f_eq t]
        calc
          ∫ t in (0)..p, f t
              = ∫ t in (0)..p,
                  ((n.choose k : ℝ) * k) * (t^(k-1) * (1-t)^(n-k)) := hcongr
          _ = (n.choose k : ℝ) * k * ∫ t in (0)..p, t^(k-1) * (1-t)^(n-k) := by
                -- Pull the constant factor out of the interval integral.
                simp [mul_comm, mul_left_comm, mul_assoc]
      -- Compare with the definition of binomial_tail_integral.
      calc
        F p = ∫ t in (0)..p, f t := by simpa [h_ftc']
        _ = (n.choose k : ℝ) * k * ∫ t in (0)..p,
              t^(k-1) * (1-t)^(n-k) := h_int_f
        _ = binomial_tail_integral n k p := by
              simp [binomial_tail_integral, mul_comm, mul_left_comm, mul_assoc]

    -- Combine probability and integral expressions in the interior case.
    simpa [h_prob] using h_eq

  · ----------------------------------------------------------------------
    -- Boundary case: k = n (since k ≤ n and not k < n)
    ----------------------------------------------------------------------
    -- From k ≤ n and ¬(k < n) we deduce k = n.
    have hkn_eq : k = n := le_antisymm hkn (le_of_not_gt hkn_lt)
    -- Rewrite everything in terms of n (eliminate k).
    have hkn_eq' : n = k := hkn_eq.symm
    subst hkn_eq'

    -- Now k has been replaced by n everywhere; in particular hk : 0 < n.
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hk

    -- Define F as the binomial tail sum for k = n, and f as its telescoping derivative.
    let F : ℝ → ℝ := fun x => ∑ i ∈ Finset.Ico n (n + 1), binomial_term n i x
    let f : ℝ → ℝ := fun x => telescoping_term n (n - 1) x

    -- The index set Ico n (n+1) is the singleton {n}.
    have hIco : Finset.Ico n (n + 1) = {n} := by
      simpa using (Nat.Ico_succ_singleton (a := n))

    -- Derivative of F is f in this boundary case.
    have h_deriv : ∀ x, HasDerivAt F (f x) x := by
      intro x
      -- Differentiate termwise using HasDerivAt.fun_sum.
      have hsum_deriv' :
          HasDerivAt (fun x => ∑ i ∈ Finset.Ico n (n + 1), binomial_term n i x)
            (∑ i ∈ Finset.Ico n (n + 1),
              (telescoping_term n (i - 1) x - telescoping_term n i x)) x := by
        refine HasDerivAt.fun_sum (u := Finset.Ico n (n + 1))
          (A := fun i x => binomial_term n i x)
          (A' := fun i => telescoping_term n (i - 1) x - telescoping_term n i x)
          (x := x) ?_
        intro i hi
        -- For i ∈ Ico n (n+1), we actually have i = n.
        have hi_eq : i = n := by
          simpa [hIco] using hi
        have hi_min : 1 ≤ i := by
          have : 1 ≤ n := hn1
          simpa [hi_eq] using this
        have hi_max : i ≤ n := by
          have : n ≤ n := le_rfl
          simpa [hi_eq] using this
        simpa [hi_eq] using binomial_term_deriv (n := n) (i := i) (x := x) hi_min hi_max
      -- Show that the last telescoping term vanishes: telescoping_term n n x = 0.
      have hcomb := combinatorial_identity_2 (n := n) (i := n)
        (hi := le_rfl) (hn := hn1)
      -- hcomb : (n.choose n : ℝ) * (n - n) = n * (n - 1).choose n
      have hzero_mul : (n : ℝ) * ((n - 1).choose n : ℝ) = 0 := by
        have : (0 : ℝ) = (n : ℝ) * ((n - 1).choose n : ℝ) := by
          simpa [Nat.choose_self] using hcomb
        simpa using this.symm
      have hn0 : (n : ℝ) ≠ 0 := by
        have : 0 < n := hk
        exact_mod_cast ne_of_gt this
      have hchoose_zero : ((n - 1).choose n : ℝ) = 0 := by
        have h := mul_eq_zero.mp hzero_mul
        cases h with
        | inl hcontra => exact (hn0 hcontra).elim
        | inr hres => exact hres
      have htel_n : telescoping_term n n x = 0 := by
        dsimp [telescoping_term]
        simp [hchoose_zero]
      -- Simplify the derivative expression using hIco and htel_n.
      have hsum_deriv :
          HasDerivAt (fun x => ∑ i ∈ Finset.Ico n (n + 1), binomial_term n i x)
            (telescoping_term n (n - 1) x) x := by
        simpa [hIco, htel_n, sub_zero] using hsum_deriv'
      -- This is exactly HasDerivAt F (f x) x.
      simpa [F, f] using hsum_deriv

    -- F(0) = 0 also holds in this boundary case.
    have hF0 : F 0 = 0 := by
      dsimp [F]
      have hn_pos : 0 < n := hk
      have hn0 : n ≠ 0 := by
        exact ne_of_gt hn_pos
      simp [hIco, binomial_term, hn_pos, hn0]  -- 0^n = 0 since n > 0

    -- Fundamental theorem of calculus for F and f.
    have h_ftc : ∫ t in (0)..p, f t = F p - F 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
      · intro x hx; exact h_deriv x
      · have hcont : Continuous f := by
          simpa [f] using continuous_telescoping_term n (n - 1)
        exact hcont.intervalIntegrable 0 p

    -- Probability side at k = n: express as F p.
    have h_prob : binomial_tail_prob p hp n n = F p := by
      have h_sum :
        binomial_tail_prob p hp n n =
          ∑ i ∈ Finset.Ico n (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) :=
        binomial_tail_sum_eq p hp n n
      simpa [F, binomial_term] using h_sum

    -- Combinatorial identity for coefficients at k = n.
    have h_coeff : (n.choose n : ℝ) * n = n * (n - 1).choose (n - 1) := by
      simpa using combinatorial_identity_1 (n := n) (i := n) (hi := hn1) (hn := hn1)

    -- f is the Beta integrand for k = n.
    have h_f_eq : ∀ t, f t = ((n.choose n : ℝ) * n) * (t^(n-1) * (1-t)^(n-n)) := by
      intro t
      dsimp [f, telescoping_term]
      rw [← h_coeff]
      have pow_eq : n - 1 - (n - 1) = (n - n) := by
        -- both sides are zero in ℕ
        simp
      simp [pow_eq, mul_left_comm, mul_assoc]

    -- Use FTC to represent F p as the integral of this integrand.
    have h_eq : F p = binomial_tail_integral n n p := by
      have h_ftc' : ∫ t in (0)..p, f t = F p := by
        have := h_ftc
        simpa [hF0, sub_zero] using this
      have h_int_f : ∫ t in (0)..p, f t =
          (n.choose n : ℝ) * n * ∫ t in (0)..p, t^(n-1) * (1-t)^(n-n) := by
        have hcongr :
            ∫ t in (0)..p, f t
              = ∫ t in (0)..p,
                  ((n.choose n : ℝ) * n) * (t^(n-1) * (1-t)^(n-n)) := by
          refine intervalIntegral.integral_congr ?_
          intro t ht; simp [h_f_eq t]
        calc
          ∫ t in (0)..p, f t
              = ∫ t in (0)..p,
                  ((n.choose n : ℝ) * n) * (t^(n-1) * (1-t)^(n-n)) := hcongr
          _ = (n.choose n : ℝ) * n * ∫ t in (0)..p, t^(n-1) * (1-t)^(n-n) := by
                simp [mul_comm, mul_left_comm, mul_assoc]
      calc
        F p = ∫ t in (0)..p, f t := by simpa [h_ftc']
        _ = (n.choose n : ℝ) * n * ∫ t in (0)..p,
              t^(n-1) * (1-t)^(n-n) := h_int_f
        _ = binomial_tail_integral n n p := by
              simp [binomial_tail_integral, mul_comm, mul_left_comm, mul_assoc]

    -- Combine the two sides in the boundary case.
    simpa [h_prob, h_eq]

open ProbabilityTheory Set in
theorem regularity_binomial_and_gaussian_gap (k : ℕ) (_ : 0 < k) :
  let n := 2 * k
  let f : ℝ → ℝ := fun x => binomial_tail_integral n k x
  let g : ℝ → ℝ := fun x =>
    let σx := Real.sqrt (x * (1 - x));
    1 - cdf (gaussianReal 0 1)
          ((1 / 2 - x) * Real.sqrt (2 * k) / σx)
      + (1 / 2) * (n.choose k : ℝ) * σx ^ n
  ContinuousOn (fun x => f x - g x) (Set.Ioc (0 : ℝ) (1 / 2 : ℝ)) ∧
  DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) ∧
  DifferentiableOn ℝ g (Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) := by
  classical
  -- Rewrite the goal to eliminate the top-level `let`-bindings and work with explicit
  -- expressions involving `2 * k`.
  change
    ContinuousOn
      (fun x =>
        binomial_tail_integral (2 * k) k x -
          (let σx := Real.sqrt (x * (1 - x));
           1 - cdf (gaussianReal 0 1)
                ((1 / 2 - x) * Real.sqrt (2 * k) / σx)
           + (1 / 2) * ((2 * k).choose k : ℝ) * σx ^ (2 * k)))
      (Set.Ioc (0 : ℝ) (1 / 2 : ℝ)) ∧
    DifferentiableOn ℝ (fun x => binomial_tail_integral (2 * k) k x)
      (Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) ∧
    DifferentiableOn ℝ
      (fun x =>
        let σx := Real.sqrt (x * (1 - x));
        1 - cdf (gaussianReal 0 1)
              ((1 / 2 - x) * Real.sqrt (2 * k) / σx)
        + (1 / 2) * ((2 * k).choose k : ℝ) * σx ^ (2 * k))
      (Set.Ioo (0 : ℝ) (1 / 2 : ℝ))

  -- First, establish global differentiability (and hence continuity) of the binomial tail
  -- integral as a function of its upper limit.
  have hF_diff_all :
      Differentiable ℝ (fun x : ℝ => binomial_tail_integral (2 * k) k x) := by
    -- Unfold the definition and use the fundamental theorem of calculus for
    -- the interval integral with variable upper limit.
    have h_int_diff :
        Differentiable ℝ
          (fun x : ℝ =>
            ∫ t in (0 : ℝ)..x,
              t ^ (k - 1) * (1 - t) ^ ((2 * k) - k)) := by
      -- The integrand is a polynomial in `t`, hence continuous.
      have h_cont_integrand :
          Continuous fun t : ℝ =>
            t ^ (k - 1) * (1 - t) ^ ((2 * k) - k) := by
        have h1 : Continuous fun t : ℝ => t ^ (k - 1) :=
          (continuous_id).pow (k - 1)
        have h2 : Continuous fun t : ℝ => (1 - t) ^ ((2 * k) - k) := by
          have h_sub : Continuous fun t : ℝ => 1 - t :=
            continuous_const.sub continuous_id
          exact h_sub.pow _
        exact h1.mul h2
      -- Apply the differentiability of the integral with variable upper limit.
      simpa using
        (intervalIntegral.differentiable_integral_of_continuous
          (a := (0 : ℝ))
          (f := fun t : ℝ => t ^ (k - 1) * (1 - t) ^ ((2 * k) - k))
          h_cont_integrand)
    -- Multiply by the constant prefactor.
    have hF : Differentiable ℝ
        (fun x : ℝ =>
          ((2 * k).choose k : ℝ) * k *
            ∫ t in (0 : ℝ)..x,
              t ^ (k - 1) * (1 - t) ^ ((2 * k) - k)) := by
      -- Use differentiability of the integral and multiplication by a constant scalar.
      have := h_int_diff.const_mul (((2 * k).choose k : ℝ) * k)
      -- The preceding line gives differentiability of
      -- `x ↦ ((2*k).choose k : ℝ) * k * ∫_0^x ...`.
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    -- Finally, rewrite back to `binomial_tail_integral`.
    simpa [binomial_tail_integral] using hF

  -- Global continuity of `F`.
  have hF_cont_all : Continuous (fun x : ℝ => binomial_tail_integral (2 * k) k x) :=
    hF_diff_all.continuous

  -- Now we will prove the three regularity properties for the explicit functions.
  refine And.intro ?h_cont ?h_diff
  · -- Continuity of the gap `F - G` on `Ioc 0 (1/2)`.
    -- Continuity of the binomial tail part on `Ioc 0 (1/2)`.
    have hF_cont :
        ContinuousOn (fun x : ℝ => binomial_tail_integral (2 * k) k x)
          (Set.Ioc (0 : ℝ) (1 / 2 : ℝ)) :=
      hF_cont_all.continuousOn

    -- Continuity of the Gaussian approximation + correction term on `Ioc 0 (1/2)`.
    have hG_cont :
        ContinuousOn
          (fun x : ℝ =>
            let σx := Real.sqrt (x * (1 - x));
            1 - cdf (gaussianReal 0 1)
                  ((1 / 2 - x) * Real.sqrt (2 * k) / σx)
              + (1 / 2) * ((2 * k).choose k : ℝ) * σx ^ (2 * k))
          (Set.Ioc (0 : ℝ) (1 / 2 : ℝ)) := by
      intro x hx
      -- From `x ∈ Ioc 0 (1/2)` we have `0 < x` and `x ≤ 1/2`.
      have hx0 : 0 < x := hx.1
      have hx_le_half : x ≤ (1 / 2 : ℝ) := hx.2
      have hx_lt_one : x < 1 := lt_of_le_of_lt hx_le_half (by norm_num)

      -- Continuity of `σx = √(x * (1 - x))` at `x`.
      have hσ_cont : ContinuousAt (fun x : ℝ => Real.sqrt (x * (1 - x))) x := by
        have hmul : ContinuousAt (fun x : ℝ => x * (1 - x)) x := by
          have h1 : ContinuousAt (fun x : ℝ => x) x := continuousAt_id
          have h2 : ContinuousAt (fun x : ℝ => 1 - x) x :=
            continuousAt_const.sub continuousAt_id
          exact h1.mul h2
        simpa using hmul.sqrt

      -- Continuity of the Gaussian argument `(1/2 - x) * √(2k) / √(x*(1-x))`.
      have h_gauss_arg :
          ContinuousAt
            (fun x : ℝ =>
              (1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x))) x := by
        -- Numerator: `(1/2 - x) * √(2k)`.
        have hnum : ContinuousAt
            (fun x : ℝ => (1 / 2 - x) * Real.sqrt (2 * k)) x := by
          have h_sub : ContinuousAt (fun x : ℝ => 1 / 2 - x) x :=
            continuousAt_const.sub continuousAt_id
          have h_const : ContinuousAt (fun _ : ℝ => Real.sqrt (2 * k)) x :=
            continuousAt_const
          exact h_sub.mul h_const
        -- Denominator: `√(x*(1-x))`, nonzero on `(0,1)`.
        have hden : ContinuousAt (fun x : ℝ => Real.sqrt (x * (1 - x))) x :=
          hσ_cont
        have hden_ne : Real.sqrt (x * (1 - x)) ≠ 0 := by
          have h_pos : 0 < x * (1 - x) := by
            have h1 : 0 < x := hx0
            have h2 : 0 < 1 - x := sub_pos.mpr hx_lt_one
            exact _root_.mul_pos h1 h2
          exact ne_of_gt (Real.sqrt_pos.mpr h_pos)
        -- Quotient rule for continuity.
        have hquot := hnum.div hden hden_ne
        simpa using hquot

      -- Continuity of the Gaussian CDF applied to the argument.
      have h_cdf_cont : ContinuousAt
          (fun x : ℝ =>
            cdf (gaussianReal 0 1)
              ((1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x)))) x := by
        -- `cdf (gaussianReal 0 1)` is differentiable everywhere, hence continuous.
        have hdiff_cdf :
            Differentiable ℝ (fun y : ℝ => cdf (gaussianReal 0 1) y) :=
          differentiable_cdf_gaussianReal
        have hcont_cdf : Continuous (fun y : ℝ => cdf (gaussianReal 0 1) y) :=
          hdiff_cdf.continuous
        -- Define the inner and outer functions explicitly to apply the composition rule.
        let g : ℝ → ℝ := fun y => cdf (gaussianReal 0 1) y
        let f : ℝ → ℝ :=
          fun x => (1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x))
        have hg : ContinuousAt g (f x) := by
          simpa [g] using (hcont_cdf.continuousAt (x := f x))
        have hf : ContinuousAt f x := by
          simpa [f] using h_gauss_arg
        have hcomp : ContinuousAt (g ∘ f) x :=
          ContinuousAt.comp (g := g) (f := f) hg hf
        simpa [g, f, Function.comp] using hcomp

      -- First term: `1 - cdf(gaussianReal 0 1)(...)`.
      have h_first : ContinuousAt
          (fun x : ℝ =>
            1 - cdf (gaussianReal 0 1)
                  ((1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x)))) x := by
        have h_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x :=
          continuousAt_const
        exact h_const.sub h_cdf_cont

      -- Second term: `(1/2)*(2k choose k)*σx^(2k)`.
      have hσpow : ContinuousAt
          (fun x : ℝ => (Real.sqrt (x * (1 - x))) ^ (2 * k)) x := by
        exact hσ_cont.pow _

      have h_second : ContinuousAt
          (fun x : ℝ =>
            (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) *
              (Real.sqrt (x * (1 - x))) ^ (2 * k)) x := by
        have h_const1 : ContinuousAt (fun _ : ℝ => (1 / 2 : ℝ)) x :=
          continuousAt_const
        have h_const2 : ContinuousAt (fun _ : ℝ => ((2 * k).choose k : ℝ)) x :=
          continuousAt_const
        have h_consts : ContinuousAt
            (fun _ : ℝ => (1 / 2 : ℝ) * ((2 * k).choose k : ℝ)) x :=
          h_const1.mul h_const2
        exact h_consts.mul hσpow

      -- Sum of the two pieces is continuous at `x`.
      have hsum : ContinuousAt
          (fun x : ℝ =>
            1 - cdf (gaussianReal 0 1)
                  ((1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x))) +
              (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) *
                (Real.sqrt (x * (1 - x))) ^ (2 * k)) x :=
        h_first.add h_second

      -- Turn continuity at `x` into continuity within `Ioc 0 (1/2)` at `x` and
      -- rewrite back in terms of the local `let`-binding for `σx`.
      have hsum_within : ContinuousWithinAt
          (fun x : ℝ =>
            1 - cdf (gaussianReal 0 1)
                  ((1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x))) +
              (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) *
                (Real.sqrt (x * (1 - x))) ^ (2 * k))
          (Set.Ioc (0 : ℝ) (1 / 2 : ℝ)) x :=
        hsum.continuousWithinAt

      -- Finally, identify this with the original expression using `σx`.
      simpa using hsum_within

    -- Combine the two pieces and use that the negative of a continuous function is continuous.
    have hG_neg :
        ContinuousOn
          (fun x : ℝ =>
            - (let σx := Real.sqrt (x * (1 - x));
               1 - cdf (gaussianReal 0 1)
                     ((1 / 2 - x) * Real.sqrt (2 * k) / σx)
                 + (1 / 2) * ((2 * k).choose k : ℝ) * σx ^ (2 * k)))
          (Set.Ioc (0 : ℝ) (1 / 2 : ℝ)) :=
      hG_cont.neg

    have h_sum :
        ContinuousOn
          (fun x : ℝ =>
            binomial_tail_integral (2 * k) k x +
              - (let σx := Real.sqrt (x * (1 - x));
                 1 - cdf (gaussianReal 0 1)
                       ((1 / 2 - x) * Real.sqrt (2 * k) / σx)
                   + (1 / 2) * ((2 * k).choose k : ℝ) * σx ^ (2 * k)))
          (Set.Ioc (0 : ℝ) (1 / 2 : ℝ)) :=
      hF_cont.add hG_neg

    -- Rewrite `f - g` as `f + (-g)`.
    simpa [sub_eq_add_neg] using h_sum

  · -- Differentiability of `F` and `G` on `Ioo 0 (1/2)`.
    refine And.intro ?h_f_diff ?h_g_diff
    · -- Differentiability of the binomial tail integral on `Ioo 0 (1/2)`.
      -- This follows from global differentiability.
      exact hF_diff_all.differentiableOn
    · -- Differentiability of the Gaussian approximation + correction term on `Ioo 0 (1/2)`.
      intro x hx
      -- From `x ∈ Ioo 0 (1/2)` we have `0 < x` and `x < 1/2`.
      have hx0 : 0 < x := hx.1
      have hx_lt_half : x < (1 / 2 : ℝ) := hx.2
      have hx_lt_one : x < 1 := lt_trans hx_lt_half (by norm_num)

      -- Positivity of the denominator `x * (1 - x)`.
      have h_mul_pos : 0 < x * (1 - x) := by
        have h1 : 0 < x := hx0
        have h2 : 0 < 1 - x := sub_pos.mpr hx_lt_one
        exact _root_.mul_pos h1 h2
      have h_mul_ne : x * (1 - x) ≠ 0 := ne_of_gt h_mul_pos

      -- Reduce differentiability within `Ioo` to differentiability on `ℝ`.
      apply DifferentiableAt.differentiableWithinAt

      -- Differentiability of `σx = √(x * (1 - x))` at `x`.
      have hσ_diff : DifferentiableAt ℝ (fun x : ℝ => Real.sqrt (x * (1 - x))) x := by
        have hmul : DifferentiableAt ℝ (fun x : ℝ => x * (1 - x)) x := by
          have h1 : DifferentiableAt ℝ (fun x : ℝ => x) x := differentiableAt_fun_id
          have h2 : DifferentiableAt ℝ (fun x : ℝ => 1 - x) x :=
            (differentiableAt_const _).sub differentiableAt_fun_id
          exact h1.mul h2
        have hne : (fun x : ℝ => x * (1 - x)) x ≠ 0 := by
          simpa using h_mul_ne
        simpa using hmul.sqrt hne

      -- Derivative of the Gaussian argument.
      have hnum_diff : DifferentiableAt ℝ
          (fun x : ℝ => (1 / 2 - x) * Real.sqrt (2 * k)) x := by
        have h_sub : DifferentiableAt ℝ (fun x : ℝ => 1 / 2 - x) x :=
          (differentiableAt_const _).sub differentiableAt_fun_id
        have h_const : DifferentiableAt ℝ (fun _ : ℝ => Real.sqrt (2 * k)) x :=
          differentiableAt_const _
        exact h_sub.mul h_const

      have hden_diff : DifferentiableAt ℝ
          (fun x : ℝ => Real.sqrt (x * (1 - x))) x := hσ_diff

      have hden_ne : Real.sqrt (x * (1 - x)) ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos.mpr h_mul_pos)

      have hφ_diff : DifferentiableAt ℝ
          (fun x : ℝ =>
            (1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x))) x := by
        have hquot := hnum_diff.div hden_diff hden_ne
        simpa using hquot

      -- Differentiability of the Gaussian CDF applied to the argument.
      have hdiff_cdf : Differentiable ℝ (fun y : ℝ => cdf (gaussianReal 0 1) y) :=
        differentiable_cdf_gaussianReal

      let g : ℝ → ℝ := fun y => cdf (gaussianReal 0 1) y
      let f : ℝ → ℝ :=
        fun x => (1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x))

      have hg : DifferentiableAt ℝ g (f x) := by
        simpa [g] using (hdiff_cdf (f x))

      have hf : DifferentiableAt ℝ f x := by
        simpa [f] using hφ_diff

      have h_cdf_diff : DifferentiableAt ℝ
          (fun x : ℝ =>
            cdf (gaussianReal 0 1)
              ((1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x)))) x := by
        have hcomp : DifferentiableAt ℝ (g ∘ f) x :=
          hg.comp x hf
        simpa [g, f, Function.comp] using hcomp

      -- First term: derivative of `1 - cdf(...)`.
      have h_first : DifferentiableAt ℝ
          (fun x : ℝ =>
            1 - cdf (gaussianReal 0 1)
                  ((1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x)))) x := by
        have h_const : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) x :=
          differentiableAt_const _
        exact h_const.sub h_cdf_diff

      -- Second term: derivative of `(1/2)*(2k choose k)*σx^(2k)`.
      have hσpow_diff : DifferentiableAt ℝ
          (fun x : ℝ => (Real.sqrt (x * (1 - x))) ^ (2 * k)) x := by
        exact hσ_diff.pow _

      have h_second : DifferentiableAt ℝ
          (fun x : ℝ =>
            (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) *
              (Real.sqrt (x * (1 - x))) ^ (2 * k)) x := by
        have h_const1 : DifferentiableAt ℝ (fun _ : ℝ => (1 / 2 : ℝ)) x :=
          differentiableAt_const _
        have h_const2 : DifferentiableAt ℝ (fun _ : ℝ => ((2 * k).choose k : ℝ)) x :=
          differentiableAt_const _
        have h_consts : DifferentiableAt ℝ
            (fun _ : ℝ => (1 / 2 : ℝ) * ((2 * k).choose k : ℝ)) x :=
          h_const1.mul h_const2
        exact h_consts.mul hσpow_diff

      -- Sum of the two differentiable pieces.
      have hsum : DifferentiableAt ℝ
          (fun x : ℝ =>
            1 - cdf (gaussianReal 0 1)
                  ((1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x))) +
              (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) *
                (Real.sqrt (x * (1 - x))) ^ (2 * k)) x :=
        h_first.add h_second

      -- Finally, identify this with the expression defined using `σx`.
      simpa using hsum

open ProbabilityTheory Filter Topology in
theorem gap_limit_at_zero (k : ℕ) (hk : 0 < k) :
  let n := 2 * k
  let gap := fun p =>
    binomial_tail_integral n k p -
      (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
             ((1 / 2 - p) * Real.sqrt (2 * k) / Real.sqrt (p * (1 - p)))
       + (1 / 2) * (n.choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ n)
  Filter.Tendsto gap (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  classical
  -- Unfold the local definitions `n` and `gap` in the goal.
  dsimp
  -- Now we use the three lemmas, one for each of the terms.
  have h_int : Filter.Tendsto (fun p : ℝ => binomial_tail_integral (2 * k) k p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    binomial_tail_integral_tendsto_zero k hk
  have h_gauss : Filter.Tendsto
      (fun p : ℝ =>
        1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
              ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    gaussian_tail_tendsto_zero k hk
  have h_corr : Filter.Tendsto
      (fun p : ℝ =>
        (1 / 2) * ((2 * k).choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ (2 * k))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    gaussian_correction_tendsto_zero k hk
  -- First, the sum of the Gaussian tail and the correction term tends to 0.
  have h_sum : Filter.Tendsto
      (fun p : ℝ =>
        (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
              ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))))
        + (1 / 2) * ((2 * k).choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ (2 * k))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    -- `Tendsto.add` gives the limit of the sum as the sum of the limits.
    simpa using Filter.Tendsto.add h_gauss h_corr
  -- The negation of this sum also tends to 0.
  have h_neg_sum : Filter.Tendsto
      (fun p : ℝ =>
        -((1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
              ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))))
          + (1 / 2) * ((2 * k).choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ (2 * k)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using h_sum.neg
  -- Now add the binomial integral term (tending to 0) and the negative sum (also 0).
  have h_gap : Filter.Tendsto
      (fun p : ℝ =>
        binomial_tail_integral (2 * k) k p
          + -((1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
                  ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))))
               + (1 / 2) * ((2 * k).choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ (2 * k)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using Filter.Tendsto.add h_int h_neg_sum
  -- Rewrite the expression as a subtraction to match the statement.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_gap

open ProbabilityTheory Filter Topology in
theorem gaussian_tail_bound_large_p_core_ineq (s : ℝ) (hs : s ∈ Set.Icc (3/16) (1/4)) :
  let u := 1 / (4 * s);
  (Real.sqrt (Real.pi) : ℝ) ≤ 2 * u^(3/2 : ℝ) * Real.exp (1 - u) := by
  classical
  -- We work with the `u` introduced by the `let` in the statement.
  -- From the bounds on `s`, we obtain bounds on `u = 1 / (4 * s)` via `gaussian_u_bounds`.
  have hu_bounds := gaussian_u_bounds s hs
  rcases hu_bounds with ⟨hu_low, hu_high⟩
  -- These bounds are exactly `1 ≤ u` and `u ≤ 4/3` since `u` is `1 / (4*s)`.
  have hu_mem : (1 / (4 * s)) ∈ Set.Icc (1 : ℝ) (4 / 3 : ℝ) := by
    refine ⟨?hle, ?hge⟩
    · -- 1 ≤ 1 / (4*s)
      simpa using hu_low
    · -- 1 / (4*s) ≤ 4/3
      simpa using hu_high
  -- Apply the pointwise bound for the core function on this interval.
  have hcore : (2 : ℝ) ≤ gaussian_core_fun (1 / (4 * s)) :=
    gaussian_core_pointwise_bound hu_mem
  -- We also have √π ≤ 2.
  have hpi : (Real.sqrt (Real.pi) : ℝ) ≤ 2 := sqrt_pi_le_two
  -- Chain inequalities: √π ≤ 2 ≤ gaussian_core_fun (1 / (4*s)).
  have hchain : (Real.sqrt (Real.pi) : ℝ) ≤ gaussian_core_fun (1 / (4 * s)) :=
    le_trans hpi hcore
  -- Unfold the definition of `gaussian_core_fun`.
  dsimp [gaussian_core_fun] at hchain
  -- Now rewrite the right-hand side in terms of the `let`-bound `u` and conclude.
  -- The goal is exactly this inequality with `u := 1 / (4*s)`.
  -- So we can discharge the goal by `simpa`.
  -- Note: the `let`-bound `u` is definitionally equal to `1 / (4*s)`.
  simpa using hchain

open ProbabilityTheory NNReal ENNReal in
lemma exists_C_sqrt_bound (a : ℝ) (n : ℕ) (hn : 0 < n) :
  ∃ C : ℝ, |a| ≤ C / √(↑n) := by
  have h_sqrt_pos : (0 : ℝ) < √(↑n) := by
    have : (0 : ℝ) < (↑n : ℝ) := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr this
  refine ⟨|a| * √(↑n), ?_⟩
  have h : |a| * √(↑n) ≤ |a| * √(↑n) := le_rfl
  exact (le_div_iff₀ h_sqrt_pos).2 h

open ProbabilityTheory NNReal ENNReal in
theorem refined_berry_esseen_bound_corrected (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
  let σ := Real.sqrt (p * (1 - p));
  let z := (k - p * n) / (σ * Real.sqrt n);
  ∃ C, |(binomial_tail_prob p hp n k + binomial_tail_prob p hp n (k + 1)) / 2 - (1 - cdf (gaussianReal 0 1) z)| ≤ C / Real.sqrt n := by
  classical
  -- Remove the auxiliary `let`-bindings for σ and z.
  simp

  -- From 0 < k ≤ n we deduce n > 0.
  have hn : 0 < n := Nat.lt_of_lt_of_le hk hkn

  -- Apply a general bound: for any real a and n > 0, we can find C with |a| ≤ C / √(↑n).
  have h :=
    exists_C_sqrt_bound
      ((binomial_tail_prob p hp n k + binomial_tail_prob p hp n (k + 1)) / 2 -
        (1 - ((cdf (gaussianReal 0 1))
              ((↑k - p * ↑n) / (√(p * (1 - p)) * √↑n)) : ℝ)))
      n hn
  -- This is exactly the desired conclusion.
  simpa using h

open ProbabilityTheory in
theorem gaussian_tail_bound_h_deriv (x : ℝ) (hx : x ∈ Set.Ioo (1/4) (1/2)) : deriv (fun x => cdf (gaussianReal 0 1) (function_A x) - (1 - x)) x = gaussianPDFReal 0 1 (function_A x) * deriv function_A x + 1 := by
  let f := fun x => cdf (gaussianReal 0 1) (function_A x)
  let g := fun x : ℝ => 1 - x

  -- Force the goal to look like a subtraction of functions
  change deriv (f - g) x = _

  have h_diff_f : DifferentiableAt ℝ f x := function_A_comp_cdf_differentiable x hx
  have h_diff_g : DifferentiableAt ℝ g x := by
    apply DifferentiableAt.sub
    · apply differentiableAt_const
    · apply differentiableAt_id

  rw [deriv_sub h_diff_f h_diff_g]

  have hx_wide : x ∈ Set.Ioo 0 (1/2) := by
    rcases hx with ⟨h1, h2⟩
    constructor <;> linarith

  rw [gaussian_deriv_comp_A x hx_wide]

  have h_deriv_g : deriv g x = -1 := by
    have : g = (fun _ => 1) - id := rfl
    rw [this]
    rw [deriv_sub]
    · rw [deriv_const, deriv_id]
      ring
    · apply differentiableAt_const
    · apply differentiableAt_id

  rw [h_deriv_g]
  ring

open ProbabilityTheory in
theorem z_limits (k : ℕ) (hk : 0 < k) : Filter.Tendsto (fun p => (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop ∧ Filter.Tendsto (fun p => (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p))) (nhdsWithin (1 / 2) (Set.Iio (1 / 2))) (nhds 0) := by
  constructor
  · -- Part 1: Limit at 0
    let f1 := fun (p : ℝ) => ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ))) / Real.sqrt (1 - p)
    let f2 := fun (p : ℝ) => Real.sqrt (1 / p)

    have h_eq : ∀ p ∈ Set.Ioo 0 1, (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p)) = f1 p * f2 p := by
      intro p hp
      dsimp [f1, f2]
      rw [Real.sqrt_mul (le_of_lt hp.1)]
      have : Real.sqrt (1 / p) = 1 / Real.sqrt p := by
        rw [one_div, Real.sqrt_inv, one_div]
      rw [this]
      field_simp [Real.sqrt_pos.mpr hp.1, Real.sqrt_pos.mpr (sub_pos.mpr hp.2)]

    have h_lim : Filter.Tendsto (fun p => f1 p * f2 p) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      let c := 1 / 2 * Real.sqrt (2 * k)
      have hc : 0 < c := by
        apply mul_pos (by norm_num)
        apply Real.sqrt_pos.mpr
        norm_num
        exact Nat.cast_pos.mpr hk

      refine Filter.Tendsto.pos_mul_atTop hc ?_ ?_
      · dsimp [f1]
        rw [show c = ((1/2 - 0) * Real.sqrt (2 * ↑k)) / Real.sqrt (1 - 0) by simp [c]]
        apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
        apply ContinuousAt.tendsto
        apply ContinuousAt.div
        · apply ContinuousAt.mul
          · exact continuousAt_const.sub continuousAt_id
          · exact continuousAt_const
        · apply ContinuousAt.sqrt
          · exact continuousAt_const.sub continuousAt_id
        · norm_num
      · dsimp [f2]
        convert tendsto_sqrt_inv_mul 1 (by norm_num)

    refine Filter.Tendsto.congr' ?_ h_lim
    filter_upwards [eventually_Ioo_of_nhdsWithin_Ioi 1 (by norm_num)] with p hp
    exact (h_eq p hp).symm

  · -- Part 2: Limit at 1/2
    rw [show (0 : ℝ) = ((1/2 - 1/2) * Real.sqrt (2 * k)) / Real.sqrt (1/2 * (1 - 1/2)) by simp]
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    apply ContinuousAt.div
    · apply ContinuousAt.mul
      · exact continuousAt_const.sub continuousAt_id
      · exact continuousAt_const
    · apply ContinuousAt.sqrt
      · apply ContinuousAt.mul
        · exact continuousAt_id
        · exact continuousAt_const.sub continuousAt_id
    · norm_num

open ProbabilityTheory Filter Topology in
theorem gaussian_limit_zero: Filter.Tendsto (fun p => ProbabilityTheory.gaussianPDFReal 0 1 (function_A p) * deriv function_A p) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨C, hC_pos, h_dom⟩ := gaussian_domination_helper
  let g := fun p : ℝ => p^(-(3/2 : ℝ)) * Real.exp (-(1/8 : ℝ)/p)
  have hg : Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine limit_aux_power_exp (3/2) (1/8) ?_
    norm_num
  refine squeeze_zero' (t₀ := nhdsWithin 0 (Set.Ioi 0)) ?_ h_dom ?_
  · filter_upwards with p using abs_nonneg _
  · have : Tendsto (fun p => C * g p) (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * 0)) :=
      Tendsto.mul tendsto_const_nhds hg
    rw [mul_zero] at this
    exact this

open Set in
theorem gaussian_tail_region2_deriv_shape: ∃ z0 > 0, ∀ z, 0 ≤ z → (z ≤ z0 → 2 / Real.sqrt Real.pi * Real.exp (-z^2) - 1 / (z^2 + 1) ^ (3/2 : ℝ) ≥ 0) ∧ (z ≥ z0 → 2 / Real.sqrt Real.pi * Real.exp (-z^2) - 1 / (z^2 + 1) ^ (3/2 : ℝ) ≤ 0) := by
  classical
  obtain ⟨z0, hz0_props, _huniq⟩ := R_aux_crossing_unique
  rcases hz0_props with ⟨hz0_pos, hz0_eq1, h_le, h_ge⟩
  refine ⟨z0, hz0_pos, ?_⟩
  intro z hz_nonneg
  constructor
  · intro hz_le_z0
    -- use 1 ≤ R_aux z when 0 ≤ z ≤ z0
    have hRaux : 1 ≤ R_aux z := h_le z hz_nonneg hz_le_z0
    -- set up abbreviations
    set A : ℝ := 2 / Real.sqrt Real.pi * Real.exp (-z^2) with hA
    set B : ℝ := (z^2 + 1) ^ (3/2 : ℝ) with hB
    have hAB : 1 ≤ A * B := by
      -- rewrite R_aux in terms of A and B
      have := hRaux
      -- R_aux z = A * B
      have hEq : R_aux z = A * B := by
        simp [R_aux, hA, hB, mul_comm, mul_left_comm, mul_assoc]
      -- turn 1 ≤ R_aux z into 1 ≤ A * B
      simpa [hEq] using this
    -- positivity of B and 1/B
    have hbase_pos : 0 < z^2 + 1 := by
      have hz2_nonneg : 0 ≤ z^2 := sq_nonneg z
      have h1 : (0 : ℝ) < 1 := zero_lt_one
      have := add_lt_add_of_le_of_lt hz2_nonneg h1
      simpa [add_comm] using this
    have hBpos : 0 < B := by
      have := Real.rpow_pos_of_pos hbase_pos (3/2 : ℝ)
      simpa [hB] using this
    have hInvB_nonneg : 0 ≤ 1 / B := by
      have h : 0 < (1 / B) := by
        have := inv_pos.mpr hBpos
        simpa [one_div] using this
      exact le_of_lt h
    -- multiply inequality by 1/B on the right
    have h_mul := mul_le_mul_of_nonneg_right hAB hInvB_nonneg
    -- simplify both sides
    have h_ineq : 1 / B ≤ A := by
      simpa [A, B, hA, hB, one_div, mul_comm, mul_left_comm, mul_assoc, hBpos.ne'] using h_mul
    -- convert to desired inequality on A - 1/B
    have h_nonneg : 0 ≤ A - 1 / B := sub_nonneg.mpr h_ineq
    -- rewrite A and B back to original expression
    have : 0 ≤ 2 / Real.sqrt Real.pi * Real.exp (-z^2) - 1 / (z^2 + 1) ^ (3/2 : ℝ) := by
      simpa [A, B, hA, hB] using h_nonneg
    -- goal is expressed with ≥ 0
    simpa [ge_iff_le] using this
  · intro hz_ge_z0
    -- use R_aux z ≤ 1 when z ≥ z0
    have hRaux : R_aux z ≤ 1 := h_ge z hz_ge_z0
    -- set up abbreviations
    set A : ℝ := 2 / Real.sqrt Real.pi * Real.exp (-z^2) with hA
    set B : ℝ := (z^2 + 1) ^ (3/2 : ℝ) with hB
    have hAB : A * B ≤ 1 := by
      have := hRaux
      have hEq : R_aux z = A * B := by
        simp [R_aux, hA, hB, mul_comm, mul_left_comm, mul_assoc]
      simpa [hEq] using this
    -- positivity of B and 1/B
    have hbase_pos : 0 < z^2 + 1 := by
      have hz2_nonneg : 0 ≤ z^2 := sq_nonneg z
      have h1 : (0 : ℝ) < 1 := zero_lt_one
      have := add_lt_add_of_le_of_lt hz2_nonneg h1
      simpa [add_comm] using this
    have hBpos : 0 < B := by
      have := Real.rpow_pos_of_pos hbase_pos (3/2 : ℝ)
      simpa [hB] using this
    have hInvB_nonneg : 0 ≤ 1 / B := by
      have h : 0 < (1 / B) := by
        have := inv_pos.mpr hBpos
        simpa [one_div] using this
      exact le_of_lt h
    -- multiply inequality by 1/B on the right
    have h_mul := mul_le_mul_of_nonneg_right hAB hInvB_nonneg
    -- simplify both sides to A ≤ 1/B
    have h_ineq : A ≤ 1 / B := by
      simpa [A, B, hA, hB, one_div, mul_comm, mul_left_comm, mul_assoc, hBpos.ne'] using h_mul
    -- turn this into A - 1/B ≤ 0
    have h_nonpos : A - 1 / B ≤ 0 := sub_nonpos.mpr h_ineq
    -- rewrite A and B back to original expression
    have : 2 / Real.sqrt Real.pi * Real.exp (-z^2) - 1 / (z^2 + 1) ^ (3/2 : ℝ) ≤ 0 := by
      simpa [A, B, hA, hB] using h_nonpos
    -- goal is expressed with ≤ 0 already
    simpa using this

open Set in
theorem psi_half_le_C (k : ℕ) (hk : 0 < k) : psi_def k (1/2) ≤ constant_C k := by
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk

  -- Evaluate psi_def at 1/2 using the given formula
  have h_psi_half : psi_def k (1/2) = -(k + 1 / 2 : ℝ) * Real.log 4 := by
    unfold psi_def
    simpa using psi_at_half k

  -- Rewrite this as a log of 1 / (2 * 4^k)
  have h_psi_log : psi_def k (1/2) = Real.log (1 / (2 * (4 : ℝ) ^ k)) := by
    calc
      psi_def k (1/2)
          = -(k + 1 / 2 : ℝ) * Real.log 4 := h_psi_half
      _   = Real.log (1 / (2 * (4 : ℝ) ^ k)) := log_one_div_two_mul_four_pow k

  -- Expand constant_C definition, introducing A and B
  unfold constant_C
  -- The `set` command gives us definitional equalities for A and B
  set A : ℝ := (1 / 2) * ((2 * k).choose k : ℝ) * k with hA_def
  set B : ℝ := Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi) with hB_def

  -- Rewrite the left-hand side using h_psi_log
  rw [h_psi_log]

  -- Positivity of the left log argument
  have h_four_pow_pos : 0 < (4 : ℝ) ^ k := by
    exact pow_pos (by norm_num) _

  have h_left_pos : 0 < 1 / (2 * (4 : ℝ) ^ k) := by
    have h_denom_pos : 0 < 2 * (4 : ℝ) ^ k := by
      have : 0 < (2 : ℝ) := by norm_num
      exact _root_.mul_pos this h_four_pow_pos
    exact one_div_pos.mpr h_denom_pos

  -- Positivity of A and B (and hence B/A)
  have h_binom_pos_nat : 0 < (2 * k).choose k := by
    -- We can use `Nat.choose_pos` with the bound k ≤ 2k
    have hk_le : k ≤ 2 * k := by
      have : k ≤ k + k := by simpa [two_mul] using Nat.le_add_left k k
      simpa [two_mul] using this
    exact Nat.choose_pos hk_le

  have h_binom_pos : 0 < ((2 * k).choose k : ℝ) := by
    exact_mod_cast h_binom_pos_nat

  have hA_pos : 0 < A := by
    -- use the defining equation for A
    have hA' : A = (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * (k : ℝ) := by
      simpa [A] using hA_def
    have : 0 < (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * (k : ℝ) := by
      have h1 : 0 < (1 / 2 : ℝ) := by norm_num
      have h2 : 0 < ((2 * k).choose k : ℝ) := h_binom_pos
      have h3 : 0 < (k : ℝ) := hk_real_pos
      exact _root_.mul_pos (mul_pos h1 h2) h3
    simpa [hA'] using this

  have hB_pos : 0 < B := by
    -- use the defining equation for B
    have hB' : B = Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi) := by
      simpa [B] using hB_def
    have : 0 < Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi) := by
      have h_sqrtk_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk_real_pos
      have h_den_pos : 0 < 4 * Real.sqrt Real.pi := by
        have : 0 < (4 : ℝ) := by norm_num
        have h_sqrtpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
        exact _root_.mul_pos this h_sqrtpi_pos
      exact div_pos h_sqrtk_pos h_den_pos
    simpa [hB'] using this

  have hBA_pos : 0 < B / A := div_pos hB_pos hA_pos

  -- Inequality between the arguments of log from BA_lower_from_central
  have h_le_args : 1 / (2 * (4 : ℝ) ^ k) ≤ B / A := by
    have h := BA_lower_from_central k hk
    -- the `set` command made A and B definitionally equal to these expressions,
    -- so we can replace them by A and B via `simpa`
    -- First, rewrite h in terms of A and B explicitly
    have h' :
        let A₀ := (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) * k
        let B₀ := Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi)
        1 / (2 * (4 : ℝ) ^ k) ≤ B₀ / A₀ := h
    simpa [A, B] using h'

  -- Use log_le_log_iff to transfer the inequality through log
  have h_log_le : Real.log (1 / (2 * (4 : ℝ) ^ k)) ≤ Real.log (B / A) := by
    have := (Real.log_le_log_iff h_left_pos hBA_pos).2 h_le_args
    exact this

  -- Finish: the right-hand side is exactly constant_C k
  simpa using h_log_le

open Set Filter Topology in
lemma Q_eighth_helper (k : ℕ) :
  (k + 1 / 2 : ℝ) - k / (4 * (1/8 : ℝ) * (1 - (1/8 : ℝ))) =
    (1/2 : ℝ) - (9/7 : ℝ) * (k : ℝ) := by
  -- simplify the denominator 4 * (1/8) * (1 - 1/8) = 7/16
  have hden : 4 * (1/8 : ℝ) * (1 - (1/8 : ℝ)) = (7/16 : ℝ) := by
    norm_num [one_div]
  -- rewrite the whole expression using hden
  have h3 : (k + 1 / 2 : ℝ) - k / (4 * (1/8 : ℝ) * (1 - (1/8 : ℝ))) =
      (k + 1 / 2 : ℝ) - k / (7/16 : ℝ) := by
    have := congrArg (fun t : ℝ => (k + 1 / 2 : ℝ) - (k : ℝ) / t) hden
    simpa using this
  -- compute the division by 7/16
  have h2 : k / (7/16 : ℝ) = (16/7 : ℝ) * (k : ℝ) := by
    field_simp
  -- now show the target equality by combining these rewrites
  have h4 : (k + 1 / 2 : ℝ) - k / (7/16 : ℝ) = (1/2 : ℝ) - (9/7 : ℝ) * (k : ℝ) := by
    have htemp : (k + 1 / 2 : ℝ) - k / (7/16 : ℝ) =
        (k + 1 / 2 : ℝ) - (16/7 : ℝ) * (k : ℝ) := by
      simpa [h2]
    have hlin : (k + 1 / 2 : ℝ) - (16/7 : ℝ) * (k : ℝ) =
        (1/2 : ℝ) - (9/7 : ℝ) * (k : ℝ) := by
      ring_nf
    exact htemp.trans hlin
  exact h3.trans h4

open Set Filter Topology in
theorem psi_unimodal (k : ℕ) (hk : 0 < k) : ∃ p0 ∈ Set.Ioo (0 : ℝ) (1/2), (∀ p ∈ Set.Ioo (0 : ℝ) p0, deriv (psi_def k) p < 0) ∧ (∀ p ∈ Set.Ioo p0 (1/2), deriv (psi_def k) p > 0) := by
  classical

  -- Auxiliary function Q appearing in the derivative factorisation
  let Q : ℝ → ℝ := fun p => (k + 1 / 2 : ℝ) - k / (4 * p * (1 - p))

  -- Real version of hk
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk

  -- 1. Derivative factorisation on (0,1/2)
  have h_deriv (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) (1/2 : ℝ)) :
      deriv (psi_def k) p = ((1 - 2 * p) / (p * (1 - p))) * Q p := by
    have h := psi_deriv k p hp
    have hfun : (fun x => psi_def k x) =
        (fun x => (k : ℝ) / (4 * x * (1 - x)) - k + (k + 1/2 : ℝ) * Real.log (x * (1 - x))) := by
      funext x
      simp [psi_def, mul_comm, mul_left_comm, mul_assoc]
    simpa [Q, hfun] using h

  -- 2. The prefactor ((1-2p)/(p(1-p))) is positive on (0,1/2)
  have h_pref_pos (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) (1/2 : ℝ)) :
      0 < (1 - 2 * p) / (p * (1 - p)) := by
    rcases hp with ⟨hp0, hp1⟩
    have hnum : 0 < 1 - 2 * p := by
      have : 2 * p < (1 : ℝ) := by
        have : p < (1/2 : ℝ) := hp1
        have h2 : (2:ℝ) * p < 2 * (1/2 : ℝ) := mul_lt_mul_of_pos_left this (by norm_num)
        simpa using h2
      exact sub_pos.mpr this
    have hden_pos : 0 < p * (1 - p) := by
      have h1 : 0 < 1 - p := sub_pos.mpr (show p < (1 : ℝ) from lt_trans hp1 (by norm_num))
      exact _root_.mul_pos hp0 h1
    exact div_pos hnum hden_pos

  -- 3. Strict monotonicity of Q on (0,1/2)
  have h_Q_increasing : StrictMonoOn Q (Set.Ioo (0 : ℝ) (1/2 : ℝ)) := by
    simpa [Q] using (Q_strictMono_Ioo_zero_half k hk)

  -- 4. Values of Q at two points: pL = 1/8 and pR = 1/2
  have hQ_at_half : 0 < Q (1/2 : ℝ) := by
    -- Here Q(1/2) = 1/2, so this is immediate.
    norm_num [Q, one_div]

  -- Q(1/8) is explicitly linear in k
  have hQ_eighth_explicit :
      Q (1/8 : ℝ) = (1/2 : ℝ) - (9/7 : ℝ) * (k : ℝ) := by
    -- unfold Q and use the helper lemma
    simpa [Q] using (Q_eighth_helper k)

  -- From the explicit formula and k ≥ 1 we get Q(1/8) < 0.
  have hQ_at_eighth : Q (1/8 : ℝ) < 0 := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hk)
    -- linear inequality in k handled by linarith
    have hneg : (1/2 : ℝ) - (9/7 : ℝ) * (k : ℝ) < 0 := by
      linarith [hk1]
    -- rewrite using the explicit formula
    have h := hneg
    rw [← hQ_eighth_explicit] at h
    exact h

  -- 5. Continuity of Q on [1/8,1/2]
  have hQ_cont : ContinuousOn Q (Set.Icc (1/8 : ℝ) (1/2 : ℝ)) := by
    -- Q(p) = (k+1/2) - k / (4*p*(1-p))
    have hpoly : Continuous fun p : ℝ => 4 * p * (1 - p) := by
      have h4 : Continuous fun _ : ℝ => (4 : ℝ) := continuous_const
      have hid : Continuous fun p : ℝ => p := continuous_id
      have hone : Continuous fun _ : ℝ => (1 : ℝ) := continuous_const
      have hsub : Continuous fun p : ℝ => 1 - p := hone.sub hid
      simpa [mul_comm, mul_left_comm, mul_assoc] using h4.mul (hid.mul hsub)
    have hden_ne : ∀ p ∈ Set.Icc (1/8 : ℝ) (1/2 : ℝ), (4 * p * (1 - p)) ≠ 0 := by
      intro p hp
      rcases hp with ⟨hpL, hpR⟩
      have hp_pos : 0 < p := by
        have : (0 : ℝ) < (1/8 : ℝ) := by norm_num
        exact lt_of_lt_of_le this hpL
      have hp_lt1 : p < (1 : ℝ) := lt_of_le_of_lt hpR (by norm_num)
      have h1p_pos : 0 < 1 - p := sub_pos.mpr hp_lt1
      have h4pos : (0 : ℝ) < (4 : ℝ) := by norm_num
      have hprod_pos : 0 < 4 * p * (1 - p) := by
        have := mul_pos h4pos (mul_pos hp_pos h1p_pos)
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      exact ne_of_gt hprod_pos
    have hrec : ContinuousOn (fun p : ℝ => (4 * p * (1 - p))⁻¹)
        (Set.Icc (1/8 : ℝ) (1/2 : ℝ)) :=
      hpoly.continuousOn.inv₀ hden_ne
    have hconst : ContinuousOn (fun _ : ℝ => (k : ℝ)) (Set.Icc (1/8 : ℝ) (1/2 : ℝ)) :=
      (continuous_const : Continuous fun _ : ℝ => (k : ℝ)).continuousOn
    have hterm : ContinuousOn (fun p : ℝ => k / (4 * p * (1 - p)))
        (Set.Icc (1/8 : ℝ) (1/2 : ℝ)) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hconst.mul hrec
    have hsum : ContinuousOn (fun p : ℝ => (k + 1/2 : ℝ) - k / (4 * p * (1 - p)))
        (Set.Icc (1/8 : ℝ) (1/2 : ℝ)) :=
      (continuous_const.continuousOn.sub hterm)
    simpa [Q] using hsum

  -- 6. Existence of p0 ∈ (1/8,1/2) with Q p0 = 0 via IVT
  have hexists_p0 : ∃ p0 ∈ Set.Ioo (1/8 : ℝ) (1/2 : ℝ), Q p0 = 0 := by
    have hQ_left : Q (1/8 : ℝ) < 0 := hQ_at_eighth
    have hQ_right : 0 < Q (1/2 : ℝ) := hQ_at_half
    have hQ_left_le : Q (1/8 : ℝ) ≤ 0 := le_of_lt hQ_left
    have hQ_right_ge : 0 ≤ Q (1/2 : ℝ) := le_of_lt hQ_right
    have hmem : (0 : ℝ) ∈ Set.Icc (Q (1/8 : ℝ)) (Q (1/2 : ℝ)) := ⟨hQ_left_le, hQ_right_ge⟩
    -- apply intermediate value theorem on [1/8,1/2]
    have hsubset := (intermediate_value_Icc (a := (1/8 : ℝ)) (b := (1/2 : ℝ))
      (f := Q) (by norm_num) hQ_cont) hmem
    rcases hsubset with ⟨p0, hp0Icc, hQp0⟩
    refine ⟨p0, ?_, ?_⟩
    · rcases hp0Icc with ⟨hp0L, hp0R⟩
      have hstrictL : (1/8 : ℝ) < p0 := by
        have hneL : p0 ≠ (1/8 : ℝ) := by
          intro h_eq
          subst h_eq
          have : Q (1/8 : ℝ) = 0 := by simpa using hQp0
          exact (ne_of_lt hQ_at_eighth) this
        exact lt_of_le_of_ne hp0L hneL.symm
      have hstrictR : p0 < (1/2 : ℝ) := by
        have hneR : p0 ≠ (1/2 : ℝ) := by
          intro h_eq
          subst h_eq
          have : Q (1/2 : ℝ) = 0 := by simpa using hQp0
          exact (ne_of_gt hQ_at_half) this
        exact lt_of_le_of_ne hp0R hneR
      exact ⟨hstrictL, hstrictR⟩
    · exact hQp0

  obtain ⟨p0, hp0I, hQp0⟩ := hexists_p0

  -- 7. p0 lies in (0,1/2)
  have hp0I_main : p0 ∈ Set.Ioo (0 : ℝ) (1/2 : ℝ) := by
    have h0lt : (0 : ℝ) < (1/8 : ℝ) := by norm_num
    exact ⟨lt_trans h0lt hp0I.1, hp0I.2⟩

  -- 8. From strict monotonicity, Q is negative to the left of p0 and positive to the right.
  have hQ_neg_left : ∀ p ∈ Set.Ioo (0 : ℝ) p0, Q p < 0 := by
    intro p hp
    rcases hp with ⟨hp0, hp_lt_p0⟩
    have hpI : p ∈ Set.Ioo (0 : ℝ) (1/2 : ℝ) := by
      refine ⟨hp0, ?_⟩
      exact lt_trans hp_lt_p0 hp0I_main.2
    have hQlt : Q p < Q p0 := h_Q_increasing hpI hp0I_main hp_lt_p0
    simpa [hQp0] using hQlt

  have hQ_pos_right : ∀ p ∈ Set.Ioo p0 (1/2 : ℝ), Q p > 0 := by
    intro p hp
    rcases hp with ⟨hp_gt_p0, hp_half⟩
    have hpI : p ∈ Set.Ioo (0 : ℝ) (1/2 : ℝ) := by
      exact ⟨hp0I_main.1.trans hp_gt_p0, hp_half⟩
    have hQlt : Q p0 < Q p := h_Q_increasing hp0I_main hpI hp_gt_p0
    simpa [hQp0] using hQlt

  -- 9. Translate sign of Q into sign of derivative using positivity of the prefactor
  refine ⟨p0, hp0I_main, ?_⟩
  constructor
  · -- derivative negative on (0,p0)
    intro p hp
    have hQI : p ∈ Set.Ioo (0 : ℝ) (1/2 : ℝ) := by
      refine ⟨hp.1, ?_⟩
      exact lt_trans hp.2 hp0I_main.2
    have hQneg := hQ_neg_left p hp
    have hpos := h_pref_pos p hQI
    have hder := h_deriv p hQI
    have hmul : ((1 - 2 * p) / (p * (1 - p))) * Q p < 0 :=
      mul_neg_of_pos_of_neg hpos hQneg
    simpa [hder] using hmul
  · -- derivative positive on (p0,1/2)
    intro p hp
    have hQI : p ∈ Set.Ioo (0 : ℝ) (1/2 : ℝ) := by
      exact ⟨hp0I_main.1.trans hp.1, hp.2⟩
    have hQpos := hQ_pos_right p hp
    have hpos := h_pref_pos p hQI
    have hder := h_deriv p hQI
    have hmul : 0 < ((1 - 2 * p) / (p * (1 - p))) * Q p :=
      mul_pos hpos hQpos
    simpa [hder] using hmul

open ProbabilityTheory NNReal ENNReal Set in
theorem pmf_binomial_tail_toReal_eq_integral (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
  ((PMF.binomial (⟨p, le_of_lt hp.1⟩) (le_of_lt hp.2) n).toMeasure
      (Set.Ici ⟨k, Nat.lt_succ_of_le hkn⟩)).toReal =
    binomial_tail_integral n k p := by
  have h1 :
      ((PMF.binomial (⟨p, le_of_lt hp.1⟩) (le_of_lt hp.2) n).toMeasure
          (Set.Ici ⟨k, Nat.lt_succ_of_le hkn⟩)).toReal =
        binomial_tail_prob p hp n k := by
    simpa using
      (pmf_binomial_tail_toReal_eq_binomial_tail_prob p hp n k hkn)
  have h2 : binomial_tail_prob p hp n k = binomial_tail_integral n k p :=
    binomial_tail_eq_integral p hp n k hk hkn
  exact h1.trans h2

open ProbabilityTheory NNReal ENNReal Finset in
lemma two_mul_sub_one_add_one (k : ℕ) (hk : 0 < k) : 2 * k - 1 + 1 = 2 * k := by
  omega

open ProbabilityTheory NNReal ENNReal Finset in
lemma final_algebra_generic (A C x : ℝ) (h : 2 * A * x = 1) :
  (A + C / 2) * x = (1 / 2 : ℝ) + (1 / 2 : ℝ) * C * x := by
  -- multiply both sides by 2 and use the hypothesis `2 * A * x = 1`
  have h_goal :
      2 * ((A + C / 2) * x) = 2 * ((1 / 2 : ℝ) + (1 / 2 : ℝ) * C * x) := by
    calc
      2 * ((A + C / 2) * x)
          = (2 * (A + C / 2)) * x := by ring
      _ = (2 * A + C) * x := by ring
      _ = 2 * A * x + C * x := by ring
      _ = (1 : ℝ) + C * x := by simpa [h]
      _ = 2 * ((1 / 2 : ℝ) + (1 / 2 : ℝ) * C * x) := by ring
  have h_two_ne : (2 : ℝ) ≠ 0 := by norm_num
  -- cancel the common factor 2 on both sides
  exact mul_left_cancel₀ h_two_ne h_goal

open ProbabilityTheory NNReal ENNReal Finset in
lemma sqrt_expr_eq_half : ((Real.sqrt (2 : ℝ))⁻¹ * Real.sqrt (1 - (2 : ℝ)⁻¹)) = (1 / 2 : ℝ) := by
  -- rewrite the inner square root in terms of `1 / 2`
  have h_one_minus : 1 - (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by
    norm_num
  have hsqrt_half : Real.sqrt (1 / 2 : ℝ) = (Real.sqrt (2 : ℝ))⁻¹ := by
    -- use `Real.sqrt_inv` with x = 2
    simpa [one_div] using (Real.sqrt_inv (2 : ℝ))
  have hsqrt : Real.sqrt (1 - (2 : ℝ)⁻¹) = (Real.sqrt (2 : ℝ))⁻¹ := by
    simpa [h_one_minus] using hsqrt_half
  -- reduce to showing (√2)⁻¹ * (√2)⁻¹ = 1 / 2
  have h_prod : ((Real.sqrt (2 : ℝ))⁻¹ * Real.sqrt (1 - (2 : ℝ)⁻¹))
      = (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt (2 : ℝ))⁻¹ := by
    simpa [hsqrt]
  -- compute (√2)⁻¹ * (√2)⁻¹ explicitly
  have h_mul : (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt (2 : ℝ))⁻¹
      = 1 / (Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ)) := by
    -- use the identity for product of reciprocals
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using
      (one_div_mul_one_div (Real.sqrt (2 : ℝ)) (Real.sqrt (2 : ℝ)))
  have h_sqr : Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ) = (2 : ℝ) := by
    -- since 2 ≥ 0, we can use `Real.mul_self_sqrt`
    have hnonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    simpa using (Real.mul_self_sqrt hnonneg)
  calc
    ((Real.sqrt (2 : ℝ))⁻¹ * Real.sqrt (1 - (2 : ℝ)⁻¹))
        = (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt (2 : ℝ))⁻¹ := h_prod
    _ = 1 / (Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ)) := h_mul
    _ = (1 / 2 : ℝ) := by simpa [h_sqr]

open ProbabilityTheory NNReal ENNReal Finset in
theorem binomial_tail_integral_half_even (k : ℕ) (hk : 0 < k) :
  let n := 2 * k
  binomial_tail_integral n k (1 / 2 : ℝ) =
    (1 / 2 : ℝ) + (1 / 2) * (n.choose k : ℝ) * (Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2))) ^ n := by
  classical
  -- We first prove the statement with `n = 2 * k` explicitly, then use `simpa` to
  -- discharge the `let n := 2 * k` in the statement.
  have main :
      binomial_tail_integral (2 * k) k (1 / 2 : ℝ) =
        (1 / 2 : ℝ) + (1 / 2 : ℝ) * ((Nat.choose (2 * k) k : ℝ)) *
          (Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2 : ℝ))) ^ (2 * k) := by
    -- basic numeric facts
    have h_k_le_n : k ≤ 2 * k := by
      have : k ≤ k + k := Nat.le_add_left _ _
      simpa [two_mul] using this
    have h_p : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by
      constructor <;> norm_num
    -- rewrite the integral as a binomial tail probability and then as a sum
    rw [← binomial_tail_eq_integral (1 / 2 : ℝ) h_p (2 * k) k hk h_k_le_n]
    rw [binomial_tail_sum_eq (1 / 2 : ℝ) h_p (2 * k) k]
    -- simplify each term in the sum at p = 1/2
    have h_term : ∀ i ∈ Finset.Ico k (2 * k + 1),
        ((2 * k).choose i : ℝ) * (1 / 2 : ℝ) ^ i * (1 - 1 / 2 : ℝ) ^ ((2 * k) - i)
          = ((2 * k).choose i : ℝ) * (1 / 2 : ℝ) ^ (2 * k) := by
      intro i hi
      rcases Finset.mem_Ico.mp hi with ⟨hki, hin_lt⟩
      have hin : i ≤ 2 * k := Nat.lt_succ_iff.mp hin_lt
      have h_add' : (2 * k) - i + i = 2 * k := Nat.sub_add_cancel hin
      have h_add : i + ((2 * k) - i) = 2 * k := by
        simpa [Nat.add_comm] using h_add'
      have h_one_minus : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
      calc
        ((2 * k).choose i : ℝ) * (1 / 2 : ℝ) ^ i * (1 - 1 / 2 : ℝ) ^ ((2 * k) - i)
            = ((2 * k).choose i : ℝ) * (1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ ((2 * k) - i) := by
                rw [h_one_minus]
        _ = ((2 * k).choose i : ℝ) * ((1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ ((2 * k) - i)) := by
                ac_rfl
        _ = ((2 * k).choose i : ℝ) * (1 / 2 : ℝ) ^ (i + ((2 * k) - i)) := by
              -- rewrite the product of powers using `pow_add`
              have hpow : (1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ ((2 * k) - i)
                  = (1 / 2 : ℝ) ^ (i + ((2 * k) - i)) := by
                simpa using (pow_add (1 / 2 : ℝ) i ((2 * k) - i)).symm
              -- apply congrArg to multiply both sides by the binomial coefficient
              have := congrArg (fun y => ((2 * k).choose i : ℝ) * y) hpow
              simpa using this
        _ = ((2 * k).choose i : ℝ) * (1 / 2 : ℝ) ^ (2 * k) := by
                simp [h_add]
    have h_sum_rewrite :
        ∑ i ∈ Finset.Ico k (2 * k + 1),
            ((2 * k).choose i : ℝ) * (1 / 2 : ℝ) ^ i * (1 - 1 / 2 : ℝ) ^ ((2 * k) - i)
          = ∑ i ∈ Finset.Ico k (2 * k + 1),
              ((2 * k).choose i : ℝ) * (1 / 2 : ℝ) ^ (2 * k) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact h_term i hi
    rw [h_sum_rewrite]
    -- factor out the constant (1/2)^(2*k) from the sum
    have h_sum_mul :
        ∑ i ∈ Finset.Ico k (2 * k + 1),
            ((2 * k).choose i : ℝ) * (1 / 2 : ℝ) ^ (2 * k)
          = (∑ i ∈ Finset.Ico k (2 * k + 1), ((2 * k).choose i : ℝ)) *
              (1 / 2 : ℝ) ^ (2 * k) := by
      simpa using
        (Finset.sum_mul
          (s := Finset.Ico k (2 * k + 1))
          (f := fun i => ((2 * k).choose i : ℝ))
          ((1 / 2 : ℝ) ^ (2 * k))).symm
    rw [h_sum_mul]
    -- relate the sum of binomial coefficients to the central-tail identity
    have hIcc_Ico :
        Finset.Icc k (2 * k) = Finset.Ico k (2 * k + 1) := by
      ext i; constructor
      · intro hi
        rcases Finset.mem_Icc.mp hi with ⟨hki, hin_le⟩
        have hin_lt : i < 2 * k + 1 := Nat.lt_succ_iff.mpr hin_le
        exact Finset.mem_Ico.mpr ⟨hki, hin_lt⟩
      · intro hi
        rcases Finset.mem_Ico.mp hi with ⟨hki, hin_lt⟩
        have hin_le : i ≤ 2 * k := Nat.lt_succ_iff.mp hin_lt
        exact Finset.mem_Icc.mpr ⟨hki, hin_le⟩
    have h_sum_eval :
        ∑ i ∈ Finset.Ico k (2 * k + 1), ((2 * k).choose i : ℝ)
          = (2 : ℝ) ^ (2 * k - 1) + ((2 * k).choose k : ℝ) / 2 := by
      simpa [hIcc_Ico] using (central_tail_sum_even_int k hk)
    rw [h_sum_eval]
    -- now we just need to perform the final algebraic simplification
    -- we derive the hypothesis `2 * A * x = 1` with A = 2^(2*k-1), x = (1/2)^(2*k),
    -- and apply `final_algebra_generic`, then rewrite the square-root factor.
    have h_cancel :
        (2 : ℝ) ^ (2 * k) * (1 / 2 : ℝ) ^ (2 * k) = (1 : ℝ) := by
      -- (2 * (1/2))^(2*k) = 1
      have h := mul_pow (2 : ℝ) (1 / 2 : ℝ) (2 * k)
      have h_two : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
      have : (2 : ℝ) ^ (2 * k) * (1 / 2 : ℝ) ^ (2 * k) = (2 * (1 / 2 : ℝ)) ^ (2 * k) := by
        simpa [mul_comm] using h.symm
      simpa [h_two] using this
    have h_two_mul :
        (2 : ℝ) * (2 : ℝ) ^ (2 * k - 1) = (2 : ℝ) ^ (2 * k) := by
      -- from `pow_succ` with exponent `2*k - 1` and simple arithmetic on ℕ
      have h := pow_succ (2 : ℝ) (2 * k - 1)
      -- h : 2 ^ (2 * k - 1 + 1) = 2 ^ (2 * k - 1) * 2
      have h' : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ (2 * k - 1) * 2 := by
        simpa [two_mul_sub_one_add_one k hk] using h
      have h_symm := h'.symm
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_symm
    have hA :
        2 * (2 : ℝ) ^ (2 * k - 1) * (1 / 2 : ℝ) ^ (2 * k) = 1 := by
      -- multiply `h_two_mul` by `(1/2)^(2*k)` and use `h_cancel`
      have h_mul := congrArg (fun t => t * (1 / 2 : ℝ) ^ (2 * k)) h_two_mul
      -- h_mul : (2 * 2 ^ (2*k - 1)) * (1/2)^(2*k) = 2 ^ (2*k) * (1/2)^(2*k)
      simpa [mul_assoc, h_cancel] using h_mul
    have h_alg :=
      final_algebra_generic ((2 : ℝ) ^ (2 * k - 1)) ((2 * k).choose k : ℝ)
        ((1 / 2 : ℝ) ^ (2 * k)) hA
    -- rewrite the square-root power and (1/2)^(2*k) into the canonical form
    -- used in the statement
    simpa [sqrt_expr_eq_half, one_div, inv_pow] using h_alg
  -- finally, discharge the `let n := 2 * k` in the statement
  simpa using main

open ProbabilityTheory Set in
theorem deriv_gap_decompose (k : ℕ) (hk : 0 < k) :
  let n := 2 * k
  let gap := fun p : ℝ =>
    binomial_tail_integral n k p -
      (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
            ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p)))
         + (1 / 2) * (n.choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ n)
  ∀ p ∈ Set.Ioo 0 (1 / 2),
    let s : ℝ := p * (1 - p)
    let z : ℝ := (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt s
    let z' : ℝ := -Real.sqrt (2 * (k : ℝ)) / (4 * s ^ (3 / 2 : ℝ))
    deriv gap p =
      (1 / 2) * ((2 * k).choose k : ℝ) * k * s ^ (k - 1) +
        ProbabilityTheory.gaussianPDFReal 0 1 z * z' := by
  intro n gap p hp s z z'
  dsimp [gap]

  -- component functions
  let f : ℝ → ℝ := fun x => binomial_tail_integral n k x
  let g_gauss : ℝ → ℝ := fun x =>
    1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
        ((1 / 2 - x) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (x * (1 - x)))
  let g_corr : ℝ → ℝ := fun x =>
    (1 / 2 : ℝ) * (n.choose k : ℝ) * (Real.sqrt (x * (1 - x))) ^ n

  -- regularity from the lemma
  have h_reg := regularity_binomial_and_gaussian_gap k hk
  have h_mem : Set.Ioo (0 : ℝ) (1 / 2 : ℝ) ∈ nhds p := Ioo_mem_nhds hp.1 hp.2

  -- f is differentiable at p
  have hf_diff : DifferentiableAt ℝ f p := by
    have := h_reg.2.1.differentiableAt h_mem
    simpa [f, n] using this

  -- total g from the regularity lemma
  let g_total : ℝ → ℝ :=
    fun x =>
      let σx := Real.sqrt (x * (1 - x))
      1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
            ((1 / 2 - x) * Real.sqrt (2 * (k : ℝ)) / σx)
        + (1 / 2) * (n.choose k : ℝ) * σx ^ n

  have hg_total_diff : DifferentiableAt ℝ g_total p := by
    have := h_reg.2.2.differentiableAt h_mem
    simpa [g_total, n] using this

  -- g_total splits as gaussian part + correction part
  have g_total_eq : g_total = fun x => g_gauss x + g_corr x := by
    funext x
    dsimp [g_total, g_gauss, g_corr]

  -- differentiability of correction term
  have h_corr_diff : DifferentiableAt ℝ g_corr p := by
    -- inner function x ↦ x * (1 - x)
    have h_inner : DifferentiableAt ℝ (fun x => x * (1 - x)) p := by
      have h1 : DifferentiableAt ℝ (fun x : ℝ => x) p := differentiableAt_id
      have h2 : DifferentiableAt ℝ (fun x : ℝ => 1 - x) p :=
        (differentiableAt_const (1 : ℝ)).sub differentiableAt_id
      have h_mul : DifferentiableAt ℝ (fun x => (fun x => 1 - x) x * x) p :=
        h2.mul h1
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul
    -- sqrt of the inner function
    have h_sqrt : DifferentiableAt ℝ (fun x => Real.sqrt (x * (1 - x))) p := by
      -- nonvanishing of the argument at p
      have hx_ne : p * (1 - p) ≠ 0 := by
        have hpos_sqrt : 0 < Real.sqrt (p * (1 - p)) := sigma_pos p hp
        have hne_sqrt : Real.sqrt (p * (1 - p)) ≠ 0 := ne_of_gt hpos_sqrt
        have hpos : 0 < p * (1 - p) := (Real.sqrt_ne_zero').1 hne_sqrt
        exact ne_of_gt hpos
      exact DifferentiableAt.sqrt h_inner hx_ne
    -- power of sqrt
    have h_pow : DifferentiableAt ℝ (fun x => (Real.sqrt (x * (1 - x))) ^ n) p :=
      h_sqrt.pow n
    -- constant times the power term
    have h_corr_aux : DifferentiableAt ℝ (fun x =>
        ((1 / 2 : ℝ) * (n.choose k : ℝ)) * (Real.sqrt (x * (1 - x)) ^ n)) p :=
      (differentiableAt_const _).mul h_pow
    simpa [g_corr, mul_comm, mul_left_comm, mul_assoc] using h_corr_aux

  -- differentiability of gaussian term
  have h_gauss_diff : DifferentiableAt ℝ g_gauss p := by
    -- from g_total = g_gauss + g_corr
    have h_sub : DifferentiableAt ℝ (fun x => g_total x - g_corr x) p :=
      hg_total_diff.sub h_corr_diff
    -- identify g_gauss with g_total - g_corr
    have hfun : (fun x => g_total x - g_corr x) = g_gauss := by
      funext x
      have ht : g_total x = g_gauss x + g_corr x := by
        have := congrArg (fun h => h x) g_total_eq
        simpa using this
      simpa [ht] using add_sub_cancel (g_gauss x) (g_corr x)
    simpa [hfun] using h_sub

  -- derivative of f from the lemma
  have d_f : deriv f p = ((n.choose k) : ℝ) * k * p^(k-1) * (1-p)^(n-k) :=
    deriv_binomial_tail_prob n k p hk

  -- simplify n - k = k since n = 2*k
  have hnk : n - k = k := by
    dsimp [n] at *
    have : (2 * k : ℕ) - k = k := by omega
    simpa using this
  rw [hnk] at d_f

  -- common inner function for the Gaussian term
  let inner : ℝ → ℝ :=
    fun x => (1 / 2 - x) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (x * (1 - x))

  -- derivative of gaussian term from the lemma
  have d_gauss : deriv g_gauss p =
      - ProbabilityTheory.gaussianPDFReal 0 1 z * z' := by
    -- basic derivative formula
    have h_base := gaussian_term_deriv k p hp
    -- express in terms of g_gauss and inner
    have h_base' :
        deriv g_gauss p =
          -(ProbabilityTheory.gaussianPDFReal 0 1
              ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) /
                Real.sqrt (p * (1 - p))) *
            deriv inner p) := by
      simpa [g_gauss, inner] using h_base
    -- derivative of the inner z-term
    have hz_inner : HasDerivAt inner z' p := by
      simpa [inner, s, z'] using (z_deriv_neg k hk p hp).1
    have hz_deriv : deriv inner p = z' := hz_inner.deriv
    -- first replace the inner derivative by z'
    have h2 :
        deriv g_gauss p =
          -(ProbabilityTheory.gaussianPDFReal 0 1
              ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) /
                Real.sqrt (p * (1 - p))) * z') := by
      simpa [hz_deriv] using h_base'
    -- now identify the z-expression
    simpa [z, s] using h2

  -- derivative of correction term from the lemma
  have d_corr : deriv g_corr p =
      (1 / 2) * ((2 * k).choose k : ℝ) * k * s ^ (k - 1) * (1 - 2 * p) := by
    have hp_oo : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp.1, lt_trans hp.2 (by norm_num)⟩
    have h := deriv_correction_term k hk p hp_oo
    simpa [g_corr, s, n] using h

  -- derivative of gap using linearity
  let gap_fun : ℝ → ℝ :=
    fun p =>
      binomial_tail_integral n k p -
        (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
              ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) /
                Real.sqrt (p * (1 - p))) +
            (1 / 2) * (n.choose k : ℝ) * Real.sqrt (p * (1 - p)) ^ n)

  have h_gap_def :
      gap_fun = fun p => f p - (g_gauss p + g_corr p) := by
    funext x
    dsimp [gap_fun, f, g_gauss, g_corr]

  -- derivative of f - (g_gauss + g_corr)
  have h_deriv_gap_aux :
      deriv (fun p => f p - (g_gauss p + g_corr p)) p =
        deriv f p - (deriv g_gauss p + deriv g_corr p) := by
    -- start from deriv_sub
    have h1 := deriv_sub hf_diff (h_gauss_diff.add h_corr_diff)
    -- rewrite in the desired form
    have h1' :
        deriv (fun p => f p - (g_gauss p + g_corr p)) p =
          deriv f p - deriv (fun p => g_gauss p + g_corr p) p := by
      simpa [f] using h1
    -- derivative of the sum
    have h_add := deriv_add h_gauss_diff h_corr_diff
    calc
      deriv (fun p => f p - (g_gauss p + g_corr p)) p
          = deriv f p - deriv (fun p => g_gauss p + g_corr p) p := h1'
      _   = deriv f p - (deriv g_gauss p + deriv g_corr p) := by
             simpa [h_add]

  -- derivative of gap_fun in terms of f, g_gauss, g_corr
  have h_deriv_gap_main :
      deriv gap_fun p =
        deriv f p - (deriv g_gauss p + deriv g_corr p) := by
    simpa [gap_fun, h_gap_def] using h_deriv_gap_aux

  -- main explicit derivative of gap_fun
  have h_deriv_gap_explicit :
      deriv gap_fun p =
        ((n.choose k : ℝ) * k * p ^ (k - 1) * (1 - p) ^ k) -
          (- ProbabilityTheory.gaussianPDFReal 0 1 z * z' +
            (1 / 2) * ((2 * k).choose k : ℝ) * k * s ^ (k - 1) * (1 - 2 * p)) := by
    simpa [d_f, d_gauss, d_corr] using h_deriv_gap_main

  -- algebraic identity for the non-Gaussian part
  have h_alg := deriv_gap_algebra_identity k hk p

  -- binomial minus correction collapses to a clean term
  have h_binom_corr :
      ((n.choose k : ℝ) * k * p ^ (k - 1) * (1 - p) ^ k) -
          (1 / 2) * ((2 * k).choose k : ℝ) * k * s ^ (k - 1) * (1 - 2 * p) =
        (1 / 2) * ((2 * k).choose k : ℝ) * k * s ^ (k - 1) := by
    -- common coefficient
    let C : ℝ := ((2 * k).choose k : ℝ) * k
    -- multiply the algebraic identity by C
    have h_mul : C *
          (p ^ (k - 1) * (1 - p) ^ k -
            (1 / 2 : ℝ) * (1 - 2 * p) * s ^ (k - 1)) =
        C * ((1 / 2 : ℝ) * s ^ (k - 1)) := by
      exact congrArg (fun t : ℝ => C * t) h_alg
    -- distribute C over the subtraction
    have h_mul' :
        C * (p ^ (k - 1) * (1 - p) ^ k) -
          C * ((1 / 2 : ℝ) * (1 - 2 * p) * s ^ (k - 1)) =
        C * ((1 / 2 : ℝ) * s ^ (k - 1)) := by
      simpa [mul_sub] using h_mul
    -- relate C to the coefficients in the statement
    have hChoose : (n.choose k : ℝ) = ((2 * k).choose k : ℝ) := by
      simpa [n] using (rfl : (2 * k : ℕ).choose k = (2 * k : ℕ).choose k)
    -- rewrite h_mul' to the desired form
    simpa [C, hChoose, mul_comm, mul_left_comm, mul_assoc] using h_mul'

  -- abbreviations for the algebraic pieces
  let A : ℝ := ((n.choose k : ℝ) * k * p ^ (k - 1) * (1 - p) ^ k)
  let B : ℝ :=
    (1 / 2) * ((2 * k).choose k : ℝ) * k * s ^ (k - 1) * (1 - 2 * p)
  let G : ℝ := ProbabilityTheory.gaussianPDFReal 0 1 z * z'

  -- purely additive rearrangement: A - (-G + B) = (A - B) + G
  have h_AB : A - (-G + B) = (A - B) + G := by
    abel

  -- express deriv gap_fun via (A - B) + G
  have h_split : deriv gap_fun p = (A - B) + G := by
    calc
      deriv gap_fun p = A - (-G + B) := by
        simpa [A, B, G] using h_deriv_gap_explicit
      _ = (A - B) + G := by
        simpa [h_AB]

  -- final algebraic simplification to the desired form
  have h_final :
      deriv gap_fun p =
        (1 / 2) * ((2 * k).choose k : ℝ) * k * s ^ (k - 1) +
          ProbabilityTheory.gaussianPDFReal 0 1 z * z' := by
    -- rewrite A - B using h_binom_corr
    have hAB' : (A - B) = (1 / 2) * ((2 * k).choose k : ℝ) * k * s ^ (k - 1) := by
      simpa [A, B] using h_binom_corr
    -- substitute into h_split
    calc
      deriv gap_fun p = (A - B) + G := h_split
      _ = (1 / 2) * ((2 * k).choose k : ℝ) * k * s ^ (k - 1) + G := by
        simpa [hAB']

  -- conclude using the definition of gap
  simpa [gap, gap_fun, G] using h_final

open ProbabilityTheory Set in
lemma s_bounds (p : ℝ) (hp : p ∈ Set.Ico (1/4) (1/2)) : p * (1 - p) ∈ Set.Icc (3/16) (1/4) := by
  rcases hp with ⟨h1, h2⟩
  have h3 : 0 ≤ p := by linarith
  have h4 : p ≤ 1 := by linarith
  rw [Set.mem_Icc]
  constructor
  · nlinarith
  · nlinarith

open ProbabilityTheory Set in
theorem gaussian_tail_bound_deriv_ineq_large_p_simp (p : ℝ) (hp : p ∈ Set.Ico (1/4) (1/2)) : gaussianPDFReal 0 1 (function_A p) * deriv function_A p ≤ -1 := by
  let s := p * (1 - p)
  let u := 1 / (4 * s)

  have hp_oo : p ∈ Set.Ioo 0 1 := by
    rcases hp with ⟨h1, h2⟩
    constructor <;> linarith

  have hs_bounds : s ∈ Set.Icc (3/16) (1/4) := s_bounds p hp
  have hs_pos : 0 < s := by linarith [hs_bounds.1]

  have h_core := gaussian_tail_bound_large_p_core_ineq s hs_bounds
  dsimp [u] at h_core

  have h_core_transformed : 1 <= (Real.sqrt Real.pi)⁻¹ * (2 * u ^ (3 / 2 : ℝ) * rexp (1 - u)) := by
    rw [← mul_le_mul_iff_left₀ (Real.sqrt_pos.mpr Real.pi_pos)]
    rw [one_mul]
    rw [mul_assoc]
    conv in (_ * Real.sqrt Real.pi) => rw [mul_comm]
    rw [← mul_assoc]
    field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']
    exact h_core

  rw [gaussianPDFReal_def]
  dsimp only
  norm_num
  rw [function_A_sq_identity p hp_oo]

  have hs_eq : p * (1 - p) = s := rfl
  rw [hs_eq]

  rw [show -(1 / (2 * s) - 2) / 2 = 1 - u by { dsimp [u]; field_simp [hs_pos]; ring }]

  rw [hasDerivAt_function_A p hp_oo |> HasDerivAt.deriv]
  rw [hs_eq]

  rw [div_eq_mul_inv (-(Real.sqrt 2))]

  have h_algebra : (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ * rexp (1 - u) * (-(Real.sqrt 2) * (4 * s ^ (3 / 2 : ℝ))⁻¹) =
                   - ((Real.sqrt Real.pi)⁻¹ * (2 * u ^ (3 / 2 : ℝ) * rexp (1 - u))) := by
    dsimp [u]
    rw [neg_mul, mul_neg]
    rw [neg_inj]

    rw [Real.div_rpow zero_le_one (mul_nonneg (by norm_num) hs_pos.le)]
    rw [Real.mul_rpow (by norm_num) hs_pos.le]
    have h4 : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
        rw [show (4:ℝ) = (2:ℝ)^(2:ℝ) by rw [Real.rpow_two]; norm_num]
        rw [←Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ))]
        norm_num
    rw [h4]

    field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne', Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2), hs_pos]
    ring

  rw [h_algebra]
  rw [neg_le_neg_iff]

  exact h_core_transformed

open ProbabilityTheory NNReal ENNReal in
lemma integral_gt_n (n k : ℕ) (p : ℝ) (h : n < k) : binomial_tail_integral n k p = 0 := by
  simp [binomial_tail_integral, Nat.choose_eq_zero_of_lt h]

open ProbabilityTheory NNReal ENNReal in
theorem gaussian_tail_approx_midpoint_binomial_tail (n k : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo 0 1) (hk : 0 < k) (hkn : k ≤ n) :
  let σ := Real.sqrt (p * (1 - p));
  let z := (k - p * n) / (σ * Real.sqrt n);
  ∃ C, |(binomial_tail_integral n k p + binomial_tail_integral n (k + 1) p) / 2 - (1 - cdf (gaussianReal 0 1) z)| ≤ C / Real.sqrt n := by
  classical
  intro σ z
  have hBE :
      ∃ C,
        |(binomial_tail_prob p hp n k + binomial_tail_prob p hp n (k + 1)) / 2 -
            (1 - cdf (gaussianReal 0 1) z)| ≤
          C / Real.sqrt n := by
    simpa [σ, z] using refined_berry_esseen_bound_corrected p hp n k hk hkn
  rcases hBE with ⟨C0, hC0⟩
  cases lt_or_eq_of_le hkn with
  | inl h_lt =>
      refine ⟨C0, ?_⟩
      have h_eq_k : binomial_tail_integral n k p = binomial_tail_prob p hp n k := by
        symm
        exact binomial_tail_eq_integral p hp n k hk hkn
      have hkn_succ : k + 1 ≤ n := Nat.succ_le_of_lt h_lt
      have h_eq_k1 :
          binomial_tail_integral n (k + 1) p =
            binomial_tail_prob p hp n (k + 1) := by
        symm
        exact binomial_tail_eq_integral p hp n (k + 1) (Nat.succ_pos k) hkn_succ
      simpa [h_eq_k, h_eq_k1] using hC0
  | inr h_eq =>
      -- Edge case k = n: k + 1 > n, so the (k+1)-tail integral vanishes.
      -- We use a slightly larger constant depending on the (k+1)-tail probability.
      set P_succ := binomial_tail_prob p hp n (k + 1) with hP_succ_def
      refine ⟨C0 + |P_succ| * Real.sqrt n / 2, ?_⟩
      have h_eq_k : binomial_tail_integral n k p = binomial_tail_prob p hp n k := by
        symm
        exact binomial_tail_eq_integral p hp n k hk hkn
      have h_n_lt_k1 : n < k + 1 := by
        simpa [h_eq] using (Nat.lt_succ_self n)
      have h_integral_succ : binomial_tail_integral n (k + 1) p = 0 :=
        integral_gt_n n (k + 1) p h_n_lt_k1
      -- Shorthand for the key expressions
      let E_int :=
        (binomial_tail_integral n k p + binomial_tail_integral n (k + 1) p) / 2
      let E_prob :=
        (binomial_tail_prob p hp n k + binomial_tail_prob p hp n (k + 1)) / 2
      let rest := 1 - cdf (gaussianReal 0 1) z
      -- Difference between integral and probabilistic midpoints
      have h_diff :
          |E_int - E_prob| = |P_succ| / 2 := by
        unfold E_int E_prob
        have h' :
            (binomial_tail_integral n k p + binomial_tail_integral n (k + 1) p) / 2 -
                (binomial_tail_prob p hp n k + binomial_tail_prob p hp n (k + 1)) / 2
              = -(binomial_tail_prob p hp n (k + 1) / 2) := by
          simp [h_eq_k, h_integral_succ, add_comm, add_left_comm, add_assoc,
                add_div, sub_eq_add_neg]
        -- Take absolute values and rewrite in terms of `P_succ`.
        have := congrArg (fun x => |x|) h'
        simp [P_succ, hP_succ_def, div_eq_mul_inv] at this
        simpa [P_succ, hP_succ_def, div_eq_mul_inv] using this
      -- Bound for the probabilistic midpoint from refined_berry_esseen_bound_corrected
      have h_prob : |E_prob - rest| ≤ C0 / Real.sqrt n := by
        simpa [E_prob, rest] using hC0
      -- Triangle inequality: |E_int - rest| ≤ |E_int - E_prob| + |E_prob - rest|
      have h_triangle :
          |E_int - rest| ≤ |E_int - E_prob| + |E_prob - rest| :=
        abs_sub_le _ _ _
      -- Combine the bounds
      have h_main :
          |E_int - rest| ≤ C0 / Real.sqrt n + |P_succ| / 2 := by
        have hA : |E_int - E_prob| ≤ |P_succ| / 2 := by
          simpa [h_diff] using (le_of_eq h_diff)
        have hB : |E_prob - rest| ≤ C0 / Real.sqrt n := h_prob
        have h_sum :
            |E_int - E_prob| + |E_prob - rest| ≤
              |P_succ| / 2 + C0 / Real.sqrt n :=
          add_le_add hA hB
        exact
          le_trans h_triangle (by simpa [add_comm] using h_sum)
      -- Rewrite the constant on the right-hand side
      have h_n_pos_nat : 0 < n := lt_of_lt_of_le hk hkn
      have h_n_pos : 0 < (n : ℝ) := by exact_mod_cast h_n_pos_nat
      have h_sqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr h_n_pos
      have h_sqrt_ne_zero : (Real.sqrt (n : ℝ)) ≠ 0 := ne_of_gt h_sqrt_pos
      have hC_eq :
          C0 / Real.sqrt n + |P_succ| / 2 =
            (C0 + |P_succ| * Real.sqrt n / 2) / Real.sqrt n := by
        field_simp [h_sqrt_ne_zero, mul_comm, mul_left_comm, mul_assoc,
          add_comm, add_left_comm, add_assoc]
      have h_final :
          |E_int - rest| ≤ (C0 + |P_succ| * Real.sqrt n / 2) / Real.sqrt n := by
        have := h_main
        simpa [hC_eq] using this
      -- Finally, rewrite `E_int` and `rest` back to the original expression.
      simpa [E_int, rest] using h_final

open Set in
theorem z_attains_value (k : ℕ) (hk : 0 < k) (y : ℝ) (hy : 0 < y) :
  ∃ c ∈ Set.Ioo (0 : ℝ) (1 / 2),
    (1 / 2 - c) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (c * (1 - c)) = y := by
  classical
  let f : ℝ → ℝ := fun x => (1 / 2 - x) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (x * (1 - x))

  -- Continuity on (0, 1/2)
  have h_cont_oo : ContinuousOn f (Set.Ioo 0 (1 / 2)) := by
    intro x hx
    exact ((z_deriv_neg k hk x hx).1).continuousAt.continuousWithinAt

  -- Limits
  have h_lim_zero : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    (z_limits k hk).1
  have h_lim_half : Filter.Tendsto f (nhdsWithin (1 / 2) (Set.Iio (1 / 2))) (nhds 0) :=
    (z_limits k hk).2

  -- Existence of a ∈ (0, 1/4) such that f a > y
  have h_ex_a : ∃ a, a ∈ Set.Ioo (0 : ℝ) (1 / 4) ∧ f a > y := by
    have h1 : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), f x > y :=
      h_lim_zero.eventually_gt_atTop y
    have h2 : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), x ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/4)), self_mem_nhdsWithin]
      intro x hx_lt hx_gt
      exact ⟨hx_gt, hx_lt⟩
    rcases (h1.and h2).exists with ⟨a, ha_gt, ha_Ioo⟩
    exact ⟨a, ha_Ioo, ha_gt⟩
  obtain ⟨a, ha_Ioo, ha_gt⟩ := h_ex_a

  -- Existence of b ∈ (1/4, 1/2) such that f b < y
  have h_ex_b : ∃ b, b ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧ f b < y := by
    have h1 : ∀ᶠ x in nhdsWithin (1 / 2) (Set.Iio (1 / 2)), f x < y :=
      (tendsto_order.1 h_lim_half).2 y hy
    have h2 : ∀ᶠ x in nhdsWithin (1 / 2) (Set.Iio (1 / 2)), x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (1/4:ℝ) < 1/2)), self_mem_nhdsWithin]
      intro x hx_gt hx_lt
      exact ⟨hx_gt, hx_lt⟩
    rcases (h1.and h2).exists with ⟨b, hb_lt, hb_Ioo⟩
    exact ⟨b, hb_Ioo, hb_lt⟩
  obtain ⟨b, hb_Ioo, hb_lt⟩ := h_ex_b

  -- Apply IVT on [a, b]
  have hab : a ≤ b := le_of_lt (lt_trans ha_Ioo.2 hb_Ioo.1)
  have h_sub : Set.Icc a b ⊆ Set.Ioo 0 (1 / 2) := by
    intro x hx
    constructor
    · exact lt_of_lt_of_le ha_Ioo.1 hx.1
    · exact lt_of_le_of_lt hx.2 hb_Ioo.2
  have h_cont_ab : ContinuousOn f (Set.Icc a b) := h_cont_oo.mono h_sub

  have : y ∈ f '' Set.Icc a b := by
    apply intermediate_value_Icc' hab h_cont_ab
    constructor
    · exact le_of_lt hb_lt
    · exact le_of_lt ha_gt

  rcases this with ⟨c, hc_mem, hc_eq⟩
  refine ⟨c, h_sub hc_mem, hc_eq⟩

open Filter Topology ProbabilityTheory in
theorem gaussian_tail_bound_region2_z_ineq (z : ℝ) (hz : 0 ≤ z) : 2 * (1 - cdf (gaussianReal 0 1) (z * Real.sqrt 2)) ≤ 1 - z / Real.sqrt (z^2 + 1) := by
  classical

  -- Define the function g and its derivative g'
  let g : ℝ → ℝ :=
    fun z => (1 - z / Real.sqrt (z^2 + 1)) - 2 * (1 - cdf (gaussianReal 0 1) (z * Real.sqrt 2))
  let g' : ℝ → ℝ :=
    fun z => 2 / Real.sqrt Real.pi * Real.exp (-z^2) - 1 / (z^2 + 1) ^ (3/2 : ℝ)

  -- Derivative information on [0, ∞)
  have h_deriv : ∀ x, 0 ≤ x → HasDerivAt g (g' x) x := by
    intro x hx
    simpa [g, g'] using gaussian_tail_region2_g_hasDeriv x

  -- Value at 0
  have h0 : g 0 = 0 := by
    simp [g, gaussian_cdf_zero_eq_half]
    norm_num

  -- Limit at +∞
  have h_lim : Filter.Tendsto g Filter.atTop (nhds 0) := by
    simpa [g] using limit_gaussian_tail_bound_region2

  -- Shape of the derivative: nonnegative up to some point, then nonpositive
  have h_shape : ∃ x0 > 0,
      (∀ x, 0 ≤ x → x ≤ x0 → g' x ≥ 0) ∧ (∀ x, x ≥ x0 → g' x ≤ 0) := by
    obtain ⟨z0, hz0_pos, h_shape_ax⟩ := gaussian_tail_region2_deriv_shape
    refine ⟨z0, hz0_pos, ?_, ?_⟩
    · intro x hx_nonneg hx_le
      have hx := h_shape_ax x hx_nonneg
      exact (hx.1 hx_le)
    · intro x hx_ge
      have hx_nonneg : 0 ≤ x := le_trans (le_of_lt hz0_pos) hx_ge
      have hx := h_shape_ax x hx_nonneg
      exact (hx.2 hx_ge)

  -- Apply the abstract unimodality lemma to get g(x) ≥ 0 for x ≥ 0
  have h_nonneg : ∀ x, 0 ≤ x → 0 ≤ g x :=
    unimodal_nonneg_of_deriv g g' h_deriv h0 h_lim h_shape

  -- Specialize to our z ≥ 0
  have hz_nonneg : 0 ≤ g z := h_nonneg z hz

  -- Rewrite in terms of the original expression and convert to the desired inequality
  have hz_form :
      0 ≤ (1 - z / Real.sqrt (z ^ 2 + 1)) -
          2 * (1 - cdf (gaussianReal 0 1) (z * Real.sqrt 2)) := by
    simpa [g] using hz_nonneg
  exact (sub_nonneg.mp hz_form)

open Filter Topology ProbabilityTheory in
theorem psi_crossing_exists_analytic (k : ℕ) (hk : 0 < k) : let s : ℝ → ℝ := fun p : ℝ => p * (1 - p); let psi : ℝ → ℝ := fun p : ℝ => (k : ℝ) / (4 * s p) - k + (k + 1 / 2 : ℝ) * Real.log (s p); let A : ℝ := (1 / 2) * ((2 * k).choose k : ℝ) * k; let B : ℝ := Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi); let C : ℝ := Real.log (B / A); ∃ c ∈ Set.Ioo (0 : ℝ) (1 / 2), (∀ p ∈ Set.Ioo 0 c, psi p ≥ C) ∧ (∀ p ∈ Set.Ico c (1 / 2), psi p ≤ C) := by
  intro s psi A B C

  have hpsi : psi = psi_def k := by
    funext p
    simp [psi, psi_def, s]
  have hC : C = constant_C k := by
    simp [C, constant_C, A, B]

  rw [hpsi, hC]

  obtain ⟨p0, hp0_mem, h_neg, h_pos⟩ := psi_unimodal k hk
  have hp0_pos : 0 < p0 := hp0_mem.1
  have hp0_lt_half : p0 < (1/2 : ℝ) := hp0_mem.2

  -- Continuity on [p0, 1/2]
  have h_cont_right : ContinuousOn (psi_def k) (Set.Icc p0 (1/2 : ℝ)) := by
    intro x hx
    rcases hx with ⟨hx_ge, hx_le⟩
    by_cases h : x < 1/2
    · have h_ioo : x ∈ Set.Ioo 0 (1/2 : ℝ) := ⟨lt_of_lt_of_le hp0_pos hx_ge, h⟩
      -- Since Ioo 0 1/2 is open, continuousOn implies continuousAt for interior points
      have h_cont_at := (psi_continuousOn_Ioo_zero_half k).continuousAt (IsOpen.mem_nhds isOpen_Ioo h_ioo)
      exact h_cont_at.continuousWithinAt
    · have heq : x = 1/2 := le_antisymm hx_le (not_lt.1 h)
      rw [heq]
      apply ContinuousAt.continuousWithinAt
      exact psi_continuousAt_half k

  -- Strictly increasing on [p0, 1/2]
  have h_mono_right : StrictMonoOn (psi_def k) (Set.Icc p0 (1/2 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc p0 (1/2 : ℝ)) h_cont_right
    intro x hx
    rw [interior_Icc] at hx
    exact h_pos x hx

  -- Value at p0 is ≤ C
  have h_p0_le_C : psi_def k p0 ≤ constant_C k := by
    have h1 : psi_def k p0 ≤ psi_def k (1/2 : ℝ) :=
      le_of_lt (h_mono_right ⟨le_rfl, le_of_lt hp0_lt_half⟩ ⟨le_of_lt hp0_lt_half, le_rfl⟩ hp0_lt_half)
    exact le_trans h1 (psi_half_le_C k hk)

  -- Find pL
  have h_tendsto : Filter.Tendsto (psi_def k) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    psi_limit_zero k hk
  have h_event_ge : ∀ᶠ p in nhdsWithin 0 (Set.Ioi 0), constant_C k + 1 ≤ psi_def k p :=
    Filter.tendsto_atTop.1 h_tendsto (constant_C k + 1)
  have h_event_Ioo : ∀ᶠ p in nhdsWithin 0 (Set.Ioi 0), p ∈ Set.Ioo 0 p0 :=
    eventually_Ioo_of_nhdsWithin_Ioi p0 hp0_pos

  obtain ⟨pL, hpL_ge, hpL_Ioo⟩ := Filter.Eventually.exists (h_event_ge.and h_event_Ioo)
  have hpL_pos : 0 < pL := hpL_Ioo.1
  have hpL_lt_p0 : pL < p0 := hpL_Ioo.2
  have hpL_gt_C : psi_def k pL > constant_C k := lt_of_lt_of_le (lt_add_one _) hpL_ge

  -- Continuity on [pL, p0]
  have h_cont_left : ContinuousOn (psi_def k) (Set.Icc pL p0) := by
    apply ContinuousOn.mono (psi_continuousOn_Ioo_zero_half k)
    intro x hx
    exact ⟨lt_of_lt_of_le hpL_pos hx.1, lt_of_le_of_lt hx.2 hp0_lt_half⟩

  -- Strictly decreasing on [pL, p0]
  have h_anti_left : StrictAntiOn (psi_def k) (Set.Icc pL p0) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc pL p0) h_cont_left
    intro x hx
    rw [interior_Icc] at hx
    exact h_neg x ⟨lt_trans hpL_pos hx.1, hx.2⟩

  -- IVT
  have h_ivt : ∃ c ∈ Set.Icc pL p0, psi_def k c = constant_C k := by
    apply intermediate_value_Icc' (le_of_lt hpL_lt_p0) h_cont_left
    constructor
    · exact h_p0_le_C
    · exact le_of_lt hpL_gt_C

  obtain ⟨c, hc_mem, hc_eq⟩ := h_ivt
  have hc_pos : 0 < c := lt_of_lt_of_le hpL_pos hc_mem.1
  have hc_lt_half : c < (1/2 : ℝ) := lt_of_le_of_lt hc_mem.2 hp0_lt_half

  refine ⟨c, ⟨hc_pos, hc_lt_half⟩, ?_, ?_⟩

  -- Left inequality: (0, c)
  · intro p hp
    have hp_pos : 0 < p := hp.1
    have hp_lt_c : p < c := hp.2
    have h_cont_pc : ContinuousOn (psi_def k) (Set.Icc p c) := by
      apply ContinuousOn.mono (psi_continuousOn_Ioo_zero_half k)
      intro x hx
      exact ⟨lt_of_lt_of_le hp_pos hx.1, lt_of_le_of_lt hx.2 hc_lt_half⟩
    have h_anti_pc : StrictAntiOn (psi_def k) (Set.Icc p c) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc p c) h_cont_pc
      intro x hx
      rw [interior_Icc] at hx
      have hc_le_p0 : c ≤ p0 := hc_mem.2
      exact h_neg x ⟨lt_trans hp_pos hx.1, lt_of_lt_of_le hx.2 hc_le_p0⟩

    have h_le : psi_def k c < psi_def k p :=
      h_anti_pc ⟨le_rfl, le_of_lt hp_lt_c⟩ ⟨le_of_lt hp_lt_c, le_rfl⟩ hp_lt_c
    rw [hc_eq] at h_le
    exact le_of_lt h_le

  -- Right inequality: [c, 1/2)
  · intro p hp
    have hc_le_p : c ≤ p := hp.1
    have hp_lt_half_val : p < (1/2 : ℝ) := hp.2

    rcases le_or_gt p p0 with hp_le_p0 | hp_gt_p0
    · -- p in [c, p0]
      if h_eq_c : p = c then
        rw [h_eq_c, hc_eq]
      else
        have hc_lt_p : c < p := lt_of_le_of_ne hc_le_p (Ne.symm h_eq_c)
        -- Anti-mono on [c, p]
        have h_anti_cp : StrictAntiOn (psi_def k) (Set.Icc c p) := by
          apply h_anti_left.mono
          exact Set.Icc_subset_Icc hc_mem.1 hp_le_p0
        have h_lt : psi_def k p < psi_def k c := h_anti_cp ⟨le_rfl, le_of_lt hc_lt_p⟩ ⟨le_of_lt hc_lt_p, le_rfl⟩ hc_lt_p
        rw [hc_eq] at h_lt
        exact le_of_lt h_lt
    · -- p in [p0, 1/2)
      have h_mono_part : StrictMonoOn (psi_def k) (Set.Icc p0 (1/2 : ℝ)) := h_mono_right
      have h_lt : psi_def k p < psi_def k (1/2 : ℝ) :=
        h_mono_part ⟨le_of_lt hp_gt_p0, le_of_lt hp_lt_half_val⟩ ⟨le_of_lt hp0_lt_half, le_rfl⟩ hp_lt_half_val
      exact le_trans (le_of_lt h_lt) (psi_half_le_C k hk)

open ProbabilityTheory Set in
theorem gap_at_half_eq_zero (k : ℕ) (hk : 0 < k) : (binomial_tail_integral (2 * k) k (1 / 2) - (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) ((1 / 2 - 1 / 2) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (1 / 2 * (1 - 1 / 2))) + (1 / 2) * ((2 * k).choose k : ℝ) * (Real.sqrt (1 / 2 * (1 - 1 / 2))) ^ (2 * k))) = 0 := by
  have h_arg : ((1 / 2 - 1 / 2) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (1 / 2 * (1 - 1 / 2))) = 0 := by
    field_simp
    ring

  have h_cdf : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      ((1 / 2 - 1 / 2) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (1 / 2 * (1 - 1 / 2))) = 1 / 2 := by
    rw [h_arg, gaussian_cdf_zero_eq_half]

  have h_int : binomial_tail_integral (2 * k) k (1 / 2) =
      (1 / 2 : ℝ) + (1 / 2) * ((2 * k).choose k : ℝ) * (Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2))) ^ (2 * k) := by
    rw [binomial_tail_integral_half_even k hk]

  rw [h_cdf, h_int]
  ring

open ProbabilityTheory Set in
theorem deriv_gap_AB_form (k : ℕ) (hk : 0 < k) :
  let n := 2 * k;
  let gap : ℝ → ℝ := fun p =>
    binomial_tail_integral n k p -
      (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
            ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p)))
         + (1 / 2) * (n.choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ n);
  let s : ℝ → ℝ := fun p : ℝ => p * (1 - p);
  let z : ℝ → ℝ := fun p : ℝ => (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (s p);
  let A : ℝ := (1 / 2) * ((2 * k).choose k : ℝ) * k;
  let B : ℝ := Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi);
  ∀ p ∈ Set.Ioo 0 (1 / 2),
    deriv gap p =
      A * (s p) ^ (k - 1) - B * (s p) ^ (- (3 / 2 : ℝ)) * Real.exp (-(z p) ^ 2 / 2) := by
  intro n gap s z A B p hp
  have h := deriv_gap_decompose k hk p hp
  dsimp only at h
  rw [h]
  dsimp [A, B, s, z]
  rw [sub_eq_add_neg]
  congr 1
  -- Gaussian term
  rw [gaussianPDFReal_std]
  have hs_pos : 0 < p * (1 - p) := by
    rcases hp with ⟨h1, h2⟩; apply mul_pos h1; linarith

  change _ = - (Real.sqrt k / (4 * Real.sqrt Real.pi) * (p * (1 - p)) ^ (-(3 / 2) : ℝ) * _)
  rw [Real.rpow_neg (le_of_lt hs_pos)]

  have h2k_rw : Real.sqrt (2 * (k : ℝ)) = Real.sqrt 2 * Real.sqrt k := by
    rw [Real.sqrt_mul]; try norm_num; try exact Nat.cast_nonneg k
  rw [h2k_rw]

  have h2pi_rw : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul]; try norm_num; try exact Real.pi_pos.le
  rw [h2pi_rw]

  field_simp [ne_of_gt (Real.rpow_pos_of_pos hs_pos (3/2))]

  have h_base : 1 + -p = 1 - p := by ring
  rw [h_base]

  rw [div_self]
  · apply ne_of_gt
    apply Real.rpow_pos_of_pos hs_pos

open ProbabilityTheory Set in
theorem gaussian_tail_bound_k_eq_1_region1 (p : ℝ) (hp : p ∈ Set.Ico (1/4) (1/2)) : 1 - p ≤ ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (function_A p) := by
  let h := fun x => cdf (gaussianReal 0 1) (function_A x) - (1 - x)

  have h_props : ContinuousOn h (Set.Icc p (1 / 2)) ∧
      DifferentiableOn ℝ h (Set.Ioo p (1 / 2)) := by
    simpa [h] using gaussian_tail_bound_h_properties p hp

  have h_cont : ContinuousOn h (Set.Icc p (1 / 2)) := h_props.1
  have h_diff : DifferentiableOn ℝ h (Set.Ioo p (1 / 2)) := h_props.2

  have h_deriv_nonpos : ∀ x ∈ Set.Ioo p (1 / 2), deriv h x ≤ 0 := by
    intro x hx
    have hx_range : x ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
      rcases hp with ⟨hp_le, _⟩
      rcases hx with ⟨hx_p, hx_half⟩
      exact ⟨lt_of_le_of_lt hp_le hx_p, hx_half⟩

    have dh_eq : deriv h x =
        gaussianPDFReal 0 1 (function_A x) * deriv function_A x + 1 := by
      simpa [h] using gaussian_tail_bound_h_deriv x hx_range

    have hx_ico : x ∈ Set.Ico (1 / 4 : ℝ) (1 / 2) := by
      rcases hx_range with ⟨hx_gt, hx_lt⟩
      exact ⟨le_of_lt hx_gt, hx_lt⟩

    have ineq := gaussian_tail_bound_deriv_ineq_large_p_simp x hx_ico
    rw [dh_eq]
    linarith

  have h_mono : AntitoneOn h (Set.Icc p (1 / 2)) := by
    have hconv : Convex ℝ (Set.Icc p (1 / 2)) := convex_Icc _ _
    have hinterior : interior (Set.Icc p (1 / 2)) = Set.Ioo p (1 / 2) := interior_Icc
    apply antitoneOn_of_deriv_nonpos hconv h_cont
    · rw [hinterior]; exact h_diff
    · intro x hx
      rw [hinterior] at hx
      exact h_deriv_nonpos x hx

  have h_half_eq_zero : h (1 / 2) = 0 := by
    dsimp [h]
    have f_half : function_A (1 / 2) = 0 := by
      unfold function_A
      norm_num
    rw [f_half, gaussian_cdf_zero_eq_half]
    norm_num

  have h_ge_zero : 0 ≤ h p := by
    have hp_le_half : p ≤ 1 / 2 := hp.2.le
    have hp_mem : p ∈ Set.Icc p (1 / 2) := Set.left_mem_Icc.mpr hp_le_half
    have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc p (1 / 2) := Set.right_mem_Icc.mpr hp_le_half
    have h_le := h_mono hp_mem hhalf_mem hp_le_half
    rw [h_half_eq_zero] at h_le
    exact h_le

  dsimp [h] at h_ge_zero
  linarith

open ProbabilityTheory Set in
lemma aux_analytic_ineq (z : ℝ) (hz : 0 ≤ z) :
    2 * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (z * Real.sqrt 2)) ≤ 1 - z / Real.sqrt (z^2 + 1) :=
  gaussian_tail_bound_region2_z_ineq z hz

open ProbabilityTheory Set in
theorem gaussian_tail_bound_region2_analytic_ineq (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/4)) : 1 - p ≤ ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (function_A p) := by
  classical
  have hp_pos : 0 < p := hp.1
  have hp_lt_quarter : p < (1 / 4 : ℝ) := hp.2

  have h_one_sub_pos : 0 < 1 - p := by linarith
  have h_denom_pos : 0 < p * (1 - p) := mul_pos hp_pos h_one_sub_pos

  let z : ℝ := (1 / 2 - p) / Real.sqrt (p * (1 - p))

  have h_z_nonneg : 0 ≤ z := by
    have : p ≤ 1/2 := by linarith
    have num_nonneg : 0 ≤ 1/2 - p := by linarith
    exact div_nonneg num_nonneg (Real.sqrt_nonneg _)

  have h_term_eq : 1 - z / Real.sqrt (z^2 + 1) = 2 * p := by
    have hP_nonneg : 0 ≤ p * (1 - p) := le_of_lt h_denom_pos
    have hP_ne : p * (1 - p) ≠ 0 := ne_of_gt h_denom_pos

    have hz_sq : z^2 = (1 / 2 - p) ^ 2 / (p * (1 - p)) := by
      dsimp [z]
      rw [div_pow, Real.sq_sqrt hP_nonneg]

    have h_den_simp : (1 / 2 - p) ^ 2 + p * (1 - p) = 1 / 4 := by ring

    have hz_sq_plus_one : z^2 + 1 = 1 / (4 * p * (1 - p)) := by
      rw [hz_sq]
      rw [div_add_one hP_ne]
      rw [h_den_simp]
      field_simp [hP_ne]

    have hz_sq_ratio : z^2 / (z^2 + 1) = (1 - 2 * p) ^ 2 := by
      rw [div_eq_mul_inv, hz_sq_plus_one]
      rw [inv_div]
      rw [hz_sq]
      field_simp [hP_ne]
      ring

    -- rewrite z / sqrt(z^2+1) using square roots
    have h_ratio_sqrt : z / Real.sqrt (z^2 + 1) = Real.sqrt (z^2 / (z^2 + 1)) := by
      have hz_sq_nonneg : 0 ≤ z^2 := sq_nonneg z
      rw [Real.sqrt_div hz_sq_nonneg (z^2 + 1)]
      rw [Real.sqrt_sq h_z_nonneg]

    have h_one_minus_2p_nonneg : 0 ≤ 1 - 2 * p := by linarith

    have h_sqrt_eq : Real.sqrt (z^2 / (z^2 + 1)) = 1 - 2 * p := by
      rw [hz_sq_ratio, Real.sqrt_sq h_one_minus_2p_nonneg]

    rw [h_ratio_sqrt, h_sqrt_eq]
    ring

  have h_arg_eq : function_A p = z * Real.sqrt 2 := by
    dsimp [function_A, z]
    ring

  -- apply the helper in terms of z
  have h_ineq := aux_analytic_ineq z h_z_nonneg

  -- rewrite the right-hand side using h_term_eq to express it in terms of p
  rw [h_term_eq] at h_ineq

  -- rewrite the argument of the cdf using h_arg_eq to express it via function_A p
  rw [← h_arg_eq] at h_ineq

  -- divide both sides by 2>0 to obtain a simpler inequality
  linarith

open ProbabilityTheory Set Filter Topology in
theorem psi_crossing_exists (k : ℕ) (hk : 0 < k) :
  let s : ℝ → ℝ := fun p : ℝ => p * (1 - p);
  let z : ℝ → ℝ := fun p : ℝ => (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (s p);
  let A : ℝ := (1 / 2) * ((2 * k).choose k : ℝ) * k;
  let B : ℝ := Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi);
  let C : ℝ := Real.log (B / A);
  let psi : ℝ → ℝ := fun p : ℝ => (z p) ^ 2 / 2 + (k + 1 / 2 : ℝ) * Real.log (s p);
  ∃ c ∈ Set.Ioo (0 : ℝ) (1 / 2),
    (∀ p ∈ Set.Ioo 0 c, psi p ≥ C) ∧
    (∀ p ∈ Set.Ico c (1 / 2), psi p ≤ C) := by
  intro s z A B C psi
  obtain ⟨c, hc_mem, h1, h2⟩ := psi_crossing_exists_analytic k hk
  use c
  constructor
  · exact hc_mem
  · constructor
    · intro p hp
      dsimp [psi, z, s]
      have hp_ioo : p ∈ Set.Ioo 0 (1/2) := by
        simp only [Set.mem_Ioo] at hc_mem hp ⊢
        exact ⟨hp.1, lt_trans hp.2 hc_mem.2⟩
      rw [psi_closed_form k p hp_ioo]
      exact h1 p hp
    · intro p hp
      dsimp [psi, z, s]
      have hp_ioo : p ∈ Set.Ioo 0 (1/2) := by
        simp only [Set.mem_Ioo, Set.mem_Ico] at hc_mem hp ⊢
        exact ⟨lt_of_lt_of_le hc_mem.1 hp.1, hp.2⟩
      rw [psi_closed_form k p hp_ioo]
      exact h2 p hp

open ProbabilityTheory Set Filter Topology in
theorem deriv_gap_sign_iff_psi (k : ℕ) (hk : 0 < k) :
  let n := 2 * k;
  let gap : ℝ → ℝ := fun p =>
    binomial_tail_integral n k p -
      (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
            ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (p * (1 - p)))
         + (1 / 2) * (n.choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ n);
  let s : ℝ → ℝ := fun p : ℝ => p * (1 - p);
  let z : ℝ → ℝ := fun p : ℝ => (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (s p);
  let A : ℝ := (1 / 2) * ((2 * k).choose k : ℝ) * k;
  let B : ℝ := Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi);
  let C : ℝ := Real.log (B / A);
  let psi : ℝ → ℝ := fun p : ℝ => (z p) ^ 2 / 2 + (k + 1 / 2 : ℝ) * Real.log (s p);
  ∀ p ∈ Set.Ioo 0 (1 / 2),
    (deriv gap p ≥ 0 ↔ psi p ≥ C) ∧ (deriv gap p ≤ 0 ↔ psi p ≤ C) := by
  intro n gap s z A B C psi p hp

  -- Positivity helpers
  have hs_pos : 0 < s p := mul_pos hp.1 (sub_pos.mpr (lt_trans hp.2 (by norm_num)))

  have hA_pos : 0 < A := by
    dsimp only [A]
    refine mul_pos (mul_pos (by norm_num) ?_) (Nat.cast_pos.mpr hk)
    exact Nat.cast_pos.mpr (Nat.choose_pos (by linarith))

  have hB_pos : 0 < B := by
    dsimp only [B]
    apply div_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk))
    apply mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)

  -- Use the AB form lemma
  have h_deriv := deriv_gap_AB_form k hk p hp
  dsimp [n, gap, s, z, A, B] at h_deriv ⊢

  -- Define terms for clarity
  let term1 := A * (s p) ^ (k - 1)
  let term2 := B * (s p) ^ (-(3 / 2 : ℝ)) * Real.exp (-(z p) ^ 2 / 2)

  have h_deriv_eq : deriv gap p = term1 - term2 := h_deriv

  have h_term1_pos : 0 < term1 := mul_pos hA_pos (pow_pos hs_pos (k - 1))
  have h_term2_pos : 0 < term2 := mul_pos (mul_pos hB_pos (rpow_pos_of_pos hs_pos _)) (Real.exp_pos _)

  -- Logarithm properties
  have h_log_term1 : Real.log term1 = Real.log A + (k - 1) * Real.log (s p) := by
    rw [Real.log_mul hA_pos.ne' (pow_pos hs_pos _).ne']
    rw [Real.log_pow (s p) (k-1)]
    simp only [Nat.cast_sub (Nat.succ_le_of_lt hk), Nat.cast_one]

  have h_log_term2 : Real.log term2 = Real.log B - (3/2 : ℝ) * Real.log (s p) - (z p)^2 / 2 := by
    rw [Real.log_mul (mul_pos hB_pos (rpow_pos_of_pos hs_pos _)).ne' (Real.exp_pos _).ne']
    rw [Real.log_mul hB_pos.ne' (rpow_pos_of_pos hs_pos _).ne']
    rw [Real.log_rpow hs_pos, Real.log_exp]
    ring

  have h_equiv : term1 ≥ term2 ↔ psi p ≥ C := by
    rw [ge_iff_le, ge_iff_le]
    rw [← Real.log_le_log_iff h_term2_pos h_term1_pos]
    rw [h_log_term1, h_log_term2]
    dsimp [psi, C]
    rw [Real.log_div hB_pos.ne' hA_pos.ne']
    constructor <;> intro h <;> linarith

  have h_equiv_le : term1 ≤ term2 ↔ psi p ≤ C := by
    rw [← Real.log_le_log_iff h_term1_pos h_term2_pos]
    rw [h_log_term1, h_log_term2]
    dsimp [psi, C]
    rw [Real.log_div hB_pos.ne' hA_pos.ne']
    constructor <;> intro h <;> linarith

  constructor
  · rw [h_deriv_eq]
    rw [ge_iff_le]
    rw [sub_nonneg]
    rw [ge_iff_le] at h_equiv
    exact h_equiv
  · rw [h_deriv_eq]
    rw [sub_nonpos]
    exact h_equiv_le

open ProbabilityTheory Set in
theorem gaussian_tail_bound_k_eq_1_region2 (p : ℝ) (hp : p ∈ Set.Ioo 0 (1/4)) : 1 - p ≤ ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (function_A p) := by
  have h0 : 1 - p ≤ ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (function_A p) :=
    gaussian_tail_bound_region2_analytic_ineq p hp
  exact h0

open ProbabilityTheory Set in
theorem deriv_gap_shape (k : ℕ) (hk : 0 < k) : let n := 2 * k; let gap := fun p => binomial_tail_integral n k p - (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) ((1 / 2 - p) * Real.sqrt (2 * k) / Real.sqrt (p * (1 - p))) + (1 / 2) * (n.choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ n); ∃ c ∈ Set.Ioo (0 : ℝ) (1 / 2), (∀ p ∈ Set.Ioo 0 c, deriv gap p ≥ 0) ∧ (∀ p ∈ Set.Ico c (1 / 2), deriv gap p ≤ 0) := by
  classical
  -- Auxiliary quantities as in `deriv_gap_sign_iff_psi` / `psi_crossing_exists`
  let s : ℝ → ℝ := fun p : ℝ => p * (1 - p)
  let z : ℝ → ℝ := fun p : ℝ => (1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (s p)
  let A : ℝ := (1 / 2) * ((2 * k).choose k : ℝ) * k
  let B : ℝ := Real.sqrt (k : ℝ) / (4 * Real.sqrt Real.pi)
  let C : ℝ := Real.log (B / A)
  let psi : ℝ → ℝ := fun p : ℝ => z p ^ 2 / 2 + (k + 1 / 2 : ℝ) * Real.log (s p)

  -- The concrete `gap` function, with `n = 2 * k` and `s p = p * (1 - p)`
  let gap' : ℝ → ℝ := fun p : ℝ =>
    binomial_tail_integral (2 * k) k p -
      (1 -
          ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
              ((1 / 2 - p) * Real.sqrt (2 * (k : ℝ)) / Real.sqrt (s p)) +
        (1 / 2) * ((2 * k).choose k : ℝ) * (Real.sqrt (s p)) ^ (2 * k))

  -- Sign of `deriv gap'` in terms of `psi`
  have hsign :
      ∀ p ∈ Set.Ioo (0 : ℝ) (1 / 2),
        (deriv gap' p ≥ 0 ↔ psi p ≥ C) ∧ (deriv gap' p ≤ 0 ↔ psi p ≤ C) := by
    simpa [gap', s, z, A, B, C, psi] using (deriv_gap_sign_iff_psi k hk)

  -- Existence and monotonicity pattern of `psi`
  have hpsi_cross :
      ∃ c ∈ Set.Ioo (0 : ℝ) (1 / 2),
        (∀ p ∈ Set.Ioo 0 c, psi p ≥ C) ∧ (∀ p ∈ Set.Ico c (1 / 2), psi p ≤ C) := by
    simpa [s, z, A, B, C, psi] using (psi_crossing_exists k hk)

  -- Use that crossing point `c` to deduce the sign pattern of `deriv gap'`
  have h_main :
      ∃ c ∈ Set.Ioo (0 : ℝ) (1 / 2),
        (∀ p ∈ Set.Ioo 0 c, deriv gap' p ≥ 0) ∧
        (∀ p ∈ Set.Ico c (1 / 2), deriv gap' p ≤ 0) := by
    rcases hpsi_cross with ⟨c, hc_mem, hpsi_ge, hpsi_le⟩
    refine ⟨c, hc_mem, ?pos, ?nonpos⟩
    · -- On (0,c), psi ≥ C, hence deriv gap' ≥ 0
      intro p hp
      -- upgrade membership to Ioo 0 (1/2)
      have hpIoo : p ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
        rcases hp with ⟨hp0, hpc⟩
        rcases hc_mem with ⟨hc0, hc_half⟩
        exact ⟨hp0, lt_trans hpc hc_half⟩
      have h_equiv := hsign p hpIoo
      have hpsi_geC : psi p ≥ C := hpsi_ge p hp
      exact (h_equiv.1).mpr hpsi_geC
    · -- On [c,1/2), psi ≤ C, hence deriv gap' ≤ 0
      intro p hp
      have hpIoo : p ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
        rcases hp with ⟨hpc, hp_half⟩
        rcases hc_mem with ⟨hc0, hc_half⟩
        have hp0 : 0 < p := lt_of_lt_of_le hc0 hpc
        exact ⟨hp0, hp_half⟩
      have h_equiv := hsign p hpIoo
      have hpsi_leC : psi p ≤ C := hpsi_le p hp
      exact (h_equiv.2).mpr hpsi_leC

  -- Now rewrite back to the `gap` and `n` used in the statement.
  -- Unfold `gap'` and `s`, and rely on definitional equality of the `let`-bound
  -- `n` and `gap` in the statement with the explicit expressions here.
  simpa [gap', s] using h_main

open ProbabilityTheory Set in
theorem gaussian_tail_bound_k_eq_1 (p : ℝ) (hp : p ∈ Set.Ioo 0 (1 / 2)) : 1 - p ≤ cdf (gaussianReal 0 1) ((1 / 2 - p) * sqrt 2 / Real.sqrt (p * (1 - p))) := by
  have h_eq : ((1 / 2 - p) * sqrt 2 / Real.sqrt (p * (1 - p))) = function_A p := rfl
  rw [h_eq]
  rcases lt_or_ge p (1/4) with h_lt | h_ge
  · -- Case p < 1/4
    have hp_region2 : p ∈ Set.Ioo 0 (1/4) := ⟨hp.1, h_lt⟩
    exact gaussian_tail_bound_k_eq_1_region2 p hp_region2
  · -- Case p ≥ 1/4
    have hp_region1 : p ∈ Set.Ico (1/4) (1/2) := ⟨h_ge, hp.2⟩
    exact gaussian_tail_bound_k_eq_1_region1 p hp_region1

open ProbabilityTheory Set in
theorem gap_ext_regular (k : ℕ) (hk : 0 < k) :
  let n := 2 * k
  let f : ℝ → ℝ := fun x => binomial_tail_integral n k x
  let g : ℝ → ℝ := fun x =>
    let σx := Real.sqrt (x * (1 - x));
    1 - cdf (gaussianReal 0 1)
          ((1 / 2 - x) * Real.sqrt (2 * k) / σx)
      + (1 / 2) * (n.choose k : ℝ) * σx ^ n
  let gap := fun x => f x - g x
  let gap_ext := fun x : ℝ => if x ≤ 0 then 0 else gap x
  ContinuousOn gap_ext (Set.Icc 0 (1 / 2 : ℝ)) ∧
  DifferentiableOn ℝ gap_ext (Set.Ioo 0 (1 / 2 : ℝ)) ∧
  gap_ext 0 = 0 ∧ gap_ext (1 / 2) = 0 ∧
  ∃ c ∈ Set.Ioo (0 : ℝ) (1 / 2),
    (∀ x ∈ Set.Ioo 0 c, deriv gap_ext x ≥ 0) ∧
    (∀ x ∈ Set.Ico c (1 / 2), deriv gap_ext x ≤ 0) := by
  intro n f g gap gap_ext

  -- Helper: gap_ext agrees with gap on (0, ∞)
  have h_eq : ∀ x, 0 < x → gap_ext x = gap x := by
    intro x hx
    simp [gap_ext, not_le.mpr hx]

  have h_zero : gap_ext 0 = 0 := by
    simp [gap_ext]

  -- Regularity from lemma
  obtain ⟨h_cont_gap_Ioc, h_diff_f, h_diff_g⟩ := regularity_binomial_and_gaussian_gap k hk
  have h_diff_gap : DifferentiableOn ℝ gap (Set.Ioo 0 (1 / 2)) := h_diff_f.sub h_diff_g

  -- DifferentiableOn gap_ext (Ioo 0 (1/2))
  have h_diff_ext : DifferentiableOn ℝ gap_ext (Set.Ioo 0 (1 / 2)) := by
    apply DifferentiableOn.congr h_diff_gap
    intro x hx; rw [h_eq x hx.1]

  -- Value at 1/2
  have h_val_half : gap_ext (1/2) = 0 := by
    rw [h_eq (1/2) (by norm_num)]
    simp only [gap, f, g]
    rw [binomial_tail_integral_half_even k hk]
    simp only [sub_eq_zero]
    have : (1 / 2 - 1 / 2 : ℝ) = 0 := by norm_num
    rw [this]
    simp [gaussian_cdf_zero_eq_half]
    ring

  -- Derivative shape
  obtain ⟨c, hc, h_pos, h_neg⟩ := deriv_gap_shape k hk

  -- Transfer derivative
  have h_deriv_eq : ∀ x ∈ Set.Ioo 0 (1 / 2), deriv gap_ext x = deriv gap x := by
    intro x hx
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hx.1] with y hy
    exact h_eq y hy

  -- ContinuousOn gap_ext (Icc 0 (1/2))
  have h_cont_ext : ContinuousOn gap_ext (Set.Icc 0 (1 / 2)) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hpos
    · -- x = 0
      rw [ContinuousWithinAt, h_zero]
      have set_eq : Set.Icc (0:ℝ) (1/2) = {0} ∪ Set.Ioc 0 (1/2) := by
        ext y; simp [Set.mem_Icc, Set.mem_Ioc, le_iff_lt_or_eq]
      rw [set_eq, nhdsWithin_union, Filter.tendsto_sup]
      constructor
      · rw [nhdsWithin_singleton, Filter.tendsto_pure_left]
        rw [h_zero]
        exact pure_le_nhds 0
      · rw [nhdsWithin]
        have lim : Filter.Tendsto gap (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := gap_limit_at_zero k hk
        apply Filter.Tendsto.congr' _ (lim.mono_left (nhdsWithin_mono 0 (fun y (hy : y ∈ Set.Ioc 0 (1/2)) => hy.1)))
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (h_eq y hy.1).symm

    · -- x > 0
      rw [ContinuousWithinAt]
      -- Filter equality
      have nhds_eq : nhdsWithin x (Set.Icc 0 (1/2)) = nhdsWithin x (Set.Ioc 0 (1/2)) := by
        have h_inter : Set.Ioc 0 (1/2) = Set.Icc (0:ℝ) (1/2) ∩ Set.Ioi 0 := by
          ext y; simp [Set.mem_Ioc, Set.mem_Icc, Set.mem_Ioi]
          constructor
          · intro h; exact ⟨⟨le_of_lt h.1, h.2⟩, h.1⟩
          · intro h; exact ⟨h.2, h.1.2⟩
        rw [h_inter, nhdsWithin_inter]
        rw [nhdsWithin_eq_nhds.mpr (IsOpen.mem_nhds isOpen_Ioi hpos)]
        simp [inf_of_le_left (nhdsWithin_le_nhds)]
      rw [nhds_eq]

      apply ContinuousWithinAt.congr_of_eventuallyEq (h_cont_gap_Ioc x ⟨hpos, hx.2⟩)
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact h_eq y hy.1
      · exact h_eq x hpos

  refine ⟨h_cont_ext, h_diff_ext, h_zero, h_val_half, c, hc, ?_, ?_⟩
  · -- Derivative positive
    intro x hx
    have hx_Ioo : x ∈ Set.Ioo 0 (1 / 2) := ⟨hx.1, lt_trans hx.2 hc.2⟩
    rw [h_deriv_eq x hx_Ioo]
    exact h_pos x hx
  · -- Derivative negative
    intro x hx
    have hx_Ioo : x ∈ Set.Ioo 0 (1 / 2) := ⟨lt_of_lt_of_le hc.1 hx.1, hx.2⟩
    rw [h_deriv_eq x hx_Ioo]
    exact h_neg x hx

open ProbabilityTheory NNReal ENNReal Set in
theorem conjecture6_3_k_eq_1 (p : ℝ) (hp : p ∈ Set.Ioo 0 (1 / 2)) (σ : ℝ) (h_σ : σ = (p * (1 - p)).sqrt) :
  binomial_gaussian_gap p hp 1 σ ≥ (1 / 2) * ((2 * 1).choose 1) * σ ^ (2 * 1) := by
  unfold binomial_gaussian_gap
  dsimp only

  -- RHS simplification
  have h_rhs : (1 / 2 : ℝ) * ((2 * 1).choose 1) * σ ^ (2 * 1) = σ ^ 2 := by
    norm_num

  rw [h_rhs]

  -- Establish p < 1
  have h_p_lt_1 : p < 1 := lt_trans hp.2 (by norm_num)
  let hp_wide : p ∈ Set.Ioo 0 1 := ⟨hp.1, h_p_lt_1⟩

  -- Link gap definition to binomial_tail_prob
  have h_tail_eq : ENNReal.toReal (((PMF.binomial ⟨p, le_of_lt hp.1⟩ (le_of_lt h_p_lt_1) 2).map (λ i => (i : ℕ))).toMeasure (Set.Ici 1)) = binomial_tail_prob p hp_wide 2 1 := by
    unfold binomial_tail_prob
    congr

  rw [h_tail_eq]
  rw [binomial_tail_2_1 p hp_wide]

  -- Simplify σ and inequality
  rw [h_σ]
  have h_sub_nonneg : 0 ≤ p * (1 - p) := mul_nonneg (le_of_lt hp.1) (sub_nonneg.mpr (le_of_lt h_p_lt_1))
  rw [Real.sq_sqrt h_sub_nonneg]

  have h_bound := gaussian_tail_bound_k_eq_1 p hp

  -- Simplify arithmetic: 2 * 1 -> 2 in the goal term
  simp only [Nat.cast_mul, Nat.cast_one, mul_one]

  set T := cdf (gaussianReal 0 1) ((1 / 2 - p) * Real.sqrt 2 / Real.sqrt (p * (1 - p)))

  -- Now h_bound is exactly: 1 - p ≤ T

  rw [ge_iff_le]

  have h_alg : 2 * p - p ^ 2 - (1 - T) = T - (1 - p)^2 := by ring
  rw [h_alg]

  have h_rhs_alg : p * (1 - p) = 1 - p - (1 - p)^2 := by ring
  rw [h_rhs_alg]

  apply sub_le_sub_right
  exact h_bound

open ProbabilityTheory NNReal ENNReal Set in
theorem conjecture6_3_proof (p : ℝ) (h_p : p ∈ Set.Ioo 0 (1 / 2)) (k : ℕ) (hk : 0 < k) (σ : ℝ) (h_σ : σ = (p * (1 - p)).sqrt) : let hp' := p_to_nnreal_le_one p h_p; 1 - cdf (gaussianReal 0 1) ((1 / 2 - p) * Real.sqrt (2 * k : ℝ≥0) / σ) + (1 / 2) * ((2 * k).choose k) * σ ^ (2 * k) ≤ ((PMF.binomial (⟨p, le_of_lt h_p.1⟩) hp' (2 * k)).toMeasure (Set.Ici ⟨k, by omega⟩)).toReal := by
  classical
  -- Set up the standard parameter used in the auxiliary lemmas.
  let n : ℕ := 2 * k

  -- Unpack the regularity and unimodality information for the extended gap.
  have hreg := gap_ext_regular k hk
  dsimp [n] at hreg
  rcases hreg with ⟨h_cont, h_diff, h0, hhalf, c, hc, h_pos_deriv, h_neg_deriv⟩

  -- Define the extended gap function `f_ext` that appears in `gap_ext_regular`.
  let f_ext : ℝ → ℝ :=
    fun x =>
      if x ≤ 0 then 0
      else
        binomial_tail_integral n k x -
          (1 - cdf (gaussianReal 0 1)
                ((1 / 2 - x) * Real.sqrt (2 * k) / Real.sqrt (x * (1 - x))) +
            (1 / 2) * (n.choose k : ℝ) * (Real.sqrt (x * (1 - x))) ^ n)

  -- Rewrite the regularity information in terms of `f_ext`.
  have h_cont_ext :
      ContinuousOn f_ext (Set.Icc 0 (1 / 2 : ℝ)) := by
    simpa [f_ext] using h_cont

  have h_diff_ext :
      DifferentiableOn ℝ f_ext (Set.Ioo 0 (1 / 2 : ℝ)) := by
    simpa [f_ext] using h_diff

  have h0_ext : f_ext 0 = 0 := by
    simpa [f_ext] using h0

  have hhalf_ext : f_ext (1 / 2) = 0 := by
    simpa [f_ext] using hhalf

  have h_pos_deriv_ext :
      ∀ x ∈ Set.Ioo 0 c, deriv f_ext x ≥ 0 := by
    intro x hx
    simpa [f_ext] using h_pos_deriv x hx

  have h_neg_deriv_ext :
      ∀ x ∈ Set.Ico c (1 / 2), deriv f_ext x ≤ 0 := by
    intro x hx
    simpa [f_ext] using h_neg_deriv x hx

  -- Step 1: Use the unimodality lemma with `f = f_ext` and `g = 0` to deduce
  -- that `f_ext x ≥ 0` for all `x ∈ [0, 1/2]`.
  have h_ge_0 : ∀ x ∈ Set.Icc 0 (1 / 2 : ℝ), f_ext x ≥ 0 := by
    -- Define the functions `f` and `g` for the unimodality lemma.
    let f : ℝ → ℝ := f_ext
    let g : ℝ → ℝ := fun _ : ℝ => (0 : ℝ)

    -- Pointwise, `f - g` coincides with `f_ext` since `g = 0`.
    have hfg : f - g = f_ext := by
      funext x; simp [f, g, f_ext]

    -- Continuity and differentiability of `f - g` come from those of `f_ext`.
    have h_cont' :
        ContinuousOn (f - g) (Set.Icc 0 (1 / 2 : ℝ)) := by
      simpa [hfg] using h_cont_ext

    have h_diff' :
        DifferentiableOn ℝ (f - g) (Set.Ioo 0 (1 / 2 : ℝ)) := by
      simpa [hfg] using h_diff_ext

    -- Endpoint values: at 0 we have `f_ext 0 = 0`, so `f 0 ≥ g 0`.
    have ha : f 0 ≥ g 0 := by
      have : (0 : ℝ) ≤ 0 := le_rfl
      simpa [f, g, f_ext, h0_ext] using this

    -- Similarly at 1/2, using `hhalf_ext`.
    have hb : f (1 / 2) ≥ g (1 / 2) := by
      change g (1 / 2) ≤ f (1 / 2)
      -- Show that `g (1/2) = f (1/2)`.
      have hgf : g (1 / 2) = f (1 / 2) := by
        -- Both sides are equal to 0.
        calc
          g (1 / 2) = (0 : ℝ) := rfl
          _ = f_ext (1 / 2) := by
            simpa using (Eq.symm hhalf_ext)
          _ = f (1 / 2) := rfl
      exact le_of_eq hgf

    -- Derivative sign pattern for `f - g`, obtained from that of `f_ext`.
    have h_sign :
        ∃ c' ∈ Set.Ioo (0 : ℝ) (1 / 2),
          (∀ x ∈ Set.Ioo 0 c', deriv (f - g) x ≥ 0) ∧
          (∀ x ∈ Set.Ico c' (1 / 2), deriv (f - g) x ≤ 0) := by
      refine ⟨c, hc, ?_, ?_⟩
      · intro x hx
        have hx' := h_pos_deriv_ext x hx
        simpa [hfg] using hx'
      · intro x hx
        have hx' := h_neg_deriv_ext x hx
        simpa [hfg] using hx'

    -- Apply the unimodality lemma.
    have h_all :=
      unimodal_gap_lemma
        (f := f) (g := g) (a := 0) (b := (1 / 2))
        (by norm_num) h_cont' h_diff' ha hb h_sign

    -- Extract the pointwise inequality and rewrite everything in terms of
    -- `f_ext`.
    intro x hx
    have := h_all x hx
    simpa [f, g, f_ext] using this

  -- Step 2: specialize to our given `p ∈ (0, 1/2)`.
  have hp_icc : p ∈ Set.Icc 0 (1 / 2 : ℝ) := ⟨le_of_lt h_p.1, le_of_lt h_p.2⟩
  have h_gap_p_nonneg := h_ge_0 p hp_icc

  -- On `(0, 1/2)` the extended gap coincides with the true gap.
  have h_gap_p_nonneg' :
      binomial_tail_integral n k p -
        (1 - cdf (gaussianReal 0 1)
              ((1 / 2 - p) * Real.sqrt (2 * k) / Real.sqrt (p * (1 - p))) +
          (1 / 2) * (n.choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ n) ≥ 0 := by
    have hp_pos : 0 < p := h_p.1
    -- For `p > 0` the `if` in the extended gap takes the `else` branch.
    have :
        f_ext p =
          binomial_tail_integral n k p -
            (1 - cdf (gaussianReal 0 1)
                  ((1 / 2 - p) * Real.sqrt (2 * k) / Real.sqrt (p * (1 - p))) +
                (1 / 2) * (n.choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ n) := by
      have : ¬p ≤ 0 := not_le_of_gt hp_pos
      simp [f_ext, this]
    -- Rewrite `h_gap_p_nonneg` with this identification.
    simpa [this] using h_gap_p_nonneg

  -- Step 3: interpret this as `g(p) ≤ f(p)`.
  have h_le_fg :
      (1 - cdf (gaussianReal 0 1)
            ((1 / 2 - p) * Real.sqrt (2 * k) / Real.sqrt (p * (1 - p))) +
        (1 / 2) * (n.choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ n) ≤
        binomial_tail_integral n k p := by
    -- From `a - b ≥ 0` we deduce `b ≤ a`.
    exact sub_nonneg.mp h_gap_p_nonneg'

  -- Step 4: relate the binomial tail integral to the PMF tail.
  have hp01 : p ∈ Set.Ioo 0 1 := ⟨h_p.1, lt_trans h_p.2 (by norm_num)⟩
  have hkn : k ≤ n := by
    dsimp [n]
    omega

  -- First, identify the PMF tail with the integral representation, using the
  -- canonical proof `le_of_lt hp01.2` that `p ≤ 1`.
  have h_pmf_eq_integral_canonical :
      ((PMF.binomial (⟨p, le_of_lt h_p.1⟩) (le_of_lt hp01.2) n).toMeasure
          (Set.Ici ⟨k, Nat.lt_succ_of_le hkn⟩)).toReal =
        binomial_tail_integral n k p := by
    -- Use the lemma linking the PMF tail with the integral representation.
    simpa [n] using pmf_binomial_tail_toReal_eq_integral p hp01 n k hk hkn

  -- Next, replace the proof of `p ≤ 1` by `p_to_nnreal_le_one p h_p`, using
  -- proof-irrelevance for propositions.
  have h_hp_eq :
      (le_of_lt hp01.2 :
          (⟨p, le_of_lt h_p.1⟩ : ℝ≥0) ≤ 1) =
        p_to_nnreal_le_one p h_p := by
    apply Subsingleton.elim

  have h_pmf_eq_integral :
      ((PMF.binomial (⟨p, le_of_lt h_p.1⟩) (p_to_nnreal_le_one p h_p) n).toMeasure
          (Set.Ici ⟨k, Nat.lt_succ_of_le hkn⟩)).toReal =
        binomial_tail_integral n k p := by
    -- Transport `h_pmf_eq_integral_canonical` along `h_hp_eq`.
    simpa [h_hp_eq] using h_pmf_eq_integral_canonical

  -- Step 5: combine the comparison `h_le_fg` with the PMF representation.
  have h_le_pmf :
      (1 - cdf (gaussianReal 0 1)
            ((1 / 2 - p) * Real.sqrt (2 * k) / Real.sqrt (p * (1 - p))) +
        (1 / 2) * (n.choose k : ℝ) * (Real.sqrt (p * (1 - p))) ^ n) ≤
        ((PMF.binomial (⟨p, le_of_lt h_p.1⟩) (p_to_nnreal_le_one p h_p) n).toMeasure
            (Set.Ici ⟨k, Nat.lt_succ_of_le hkn⟩)).toReal := by
    -- Start from `h_le_fg` and rewrite the right-hand side.
    have h' := h_le_fg
    -- Replace `binomial_tail_integral` by the PMF tail using `h_pmf_eq_integral`.
    -- We rewrite the right-hand side of the inequality in `h'`.
    -- The lemma `h_pmf_eq_integral` has the form `measure = integral`, so we
    -- use it with symmetry.
    have h'' := h'
    rw [← h_pmf_eq_integral] at h''
    exact h''

  -- Step 6: rewrite everything in terms of the parameters in the statement.
  -- In particular, use `n = 2 * k` and `σ = sqrt (p * (1 - p))`.
  have h_final :
      1 - cdf (gaussianReal 0 1)
            ((1 / 2 - p) * Real.sqrt (2 * k : ℝ≥0) / σ) +
          (1 / 2) * ((2 * k).choose k : ℝ) * σ ^ (2 * k) ≤
        ((PMF.binomial (⟨p, le_of_lt h_p.1⟩) (p_to_nnreal_le_one p h_p) n).toMeasure
            (Set.Ici ⟨k, Nat.lt_succ_of_le hkn⟩)).toReal := by
    -- This is just a matter of unfolding `n` and `σ`.
    have hσ : σ = Real.sqrt (p * (1 - p)) := h_σ
    simpa [n, hσ] using h_le_pmf

  -- The claim of the theorem is exactly `h_final`, after unfolding `n`.
  simpa [n] using h_final

open NNReal ENNReal ProbabilityTheory

local notation "Φ" => cdf (gaussianReal 0 1)

theorem arxiv_id0911_2077_conjecture6_3 (p : ℝ) (h_p : p ∈ Set.Ioo 0 (1 / 2)) (k : ℕ) (hk : 0 < k)
    (σ : ℝ) (h_σ : σ = (p * (1 - p)).sqrt) :
    let hp' : p ≤ 1 := p_to_nnreal_le_one p h_p;
    1 - Φ ((1 / 2 - p) * Real.sqrt (2 * k : ℝ≥0) / σ)
      + (1 / 2) * ((2 * k).choose k) * σ ^ (2 * k)
      ≤ ((PMF.binomial (⟨p, le_of_lt h_p.1⟩) hp' (2 * k)).toMeasure
        (Set.Ici ⟨k, by omega⟩)).toReal := by
  classical
  simpa using
    (conjecture6_3_proof p h_p k hk σ h_σ)

#print axioms arxiv_id0911_2077_conjecture6_3
