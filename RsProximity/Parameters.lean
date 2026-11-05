import RsProximity.ListDecoding

-- ============================================================================
-- FRI parameter machinery
-- ============================================================================
--
-- The executable counterpart of the radius theory: everything here is
-- computed over ℚ, so #eval produces actual numbers. The correctness
-- lemmas tie the computed values back to the Real-valued definitions
-- of ListDecoding.lean (johnsonRadius), so a parameter set computed
-- here is certified to sit inside the proved regime.
--
-- The accounting model: a word that is δ-far from the code passes one
-- verifier query with probability at most 1 − δ, so t independent
-- queries give soundness error (1 − δ)^t. leastQueries finds the
-- least t with (1 − δ)^t ≤ 2^(−bits), by exact rational search.
--
-- Part of the RsProximity library.

namespace RsProximity

section Parameters

/-- The unique-decoding radius (1 − ρ)/2 for rate ρ = k/n, as a
rational. -/
def uniqueDecodingRadiusQ (k n : ℕ) : ℚ := (1 - (k : ℚ) / n) / 2

/-- The capacity bound 1 − ρ for rate ρ = k/n, as a rational. -/
def capacityQ (k n : ℕ) : ℚ := 1 - (k : ℚ) / n

/-- A rational lower bound on the Johnson radius 1 − √(k/n), via
Nat.sqrt: exact when k·n is a perfect square, otherwise below the true
value by less than 1/n. The point is that the bound is computable and
certifiable (johnsonLower_le_johnsonRadius). -/
def johnsonLower (k n : ℕ) : ℚ :=
  1 - ((if Nat.sqrt (k * n) ^ 2 = k * n then Nat.sqrt (k * n)
    else Nat.sqrt (k * n) + 1 : ℕ) : ℚ) / n

/-- Decidable certificate that δ sits below the Johnson radius for rate
k/n: checks k·n ≤ ((1 − δ)·n)² over ℚ, i.e. k/n ≤ (1 − δ)², squaring
out the √ρ. -/
def isBelowJohnson (δ : ℚ) (k n : ℕ) : Bool :=
  decide (0 ≤ 1 - δ ∧ (k * n : ℚ) ≤ ((1 - δ) * n) ^ 2)

/-- The certificate is sound: a δ passing isBelowJohnson is, as a real,
below the library's johnsonRadius, hence inside the proved
Guruswami–Sudan / BCIKS regime. -/
theorem le_johnsonRadius_of_isBelowJohnson {δ : ℚ} {k n : ℕ} (hn : 0 < n)
    (h : isBelowJohnson δ k n) :
    (δ : ℝ) ≤ johnsonRadius ((k : ℝ) / n) := by
  unfold isBelowJohnson at h
  rw [decide_eq_true_eq] at h
  obtain ⟨hδ0, hsq⟩ := h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ0R : (0 : ℝ) ≤ 1 - δ := by exact_mod_cast hδ0
  have hsqR : ((k * n : ℕ) : ℝ) ≤ (((1 - δ) * n : ℚ) : ℝ) ^ 2 := by
    exact_mod_cast hsq
  push_cast at hsqR
  rw [mul_pow] at hsqR
  have hkn : (k : ℝ) / n ≤ (1 - δ) ^ 2 := by
    rw [div_le_iff₀ hnR]
    nlinarith [hsqR, hnR]
  have hsqrt : Real.sqrt ((k : ℝ) / n) ≤ 1 - δ :=
    Real.sqrt_le_iff.mpr ⟨hδ0R, hkn⟩
  unfold johnsonRadius
  linarith

/-- The computed lower bound is certified: it passes its own check,
and is therefore below the real Johnson radius. -/
theorem johnsonLower_le_johnsonRadius {k n : ℕ} (hn : 0 < n) :
    ((johnsonLower k n : ℚ) : ℝ) ≤ johnsonRadius ((k : ℝ) / n) := by
  apply le_johnsonRadius_of_isBelowJohnson hn
  unfold isBelowJohnson johnsonLower
  rw [decide_eq_true_eq]
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  set s := Nat.sqrt (k * n) with hs
  constructor
  · split
    · have hsimp : (1 : ℚ) - (1 - (s : ℚ) / n) = (s : ℚ) / n := by ring_nf
      rw [hsimp]
      positivity
    · have hsimp : (1 : ℚ) - (1 - ((s + 1 : ℕ) : ℚ) / n) = ((s + 1 : ℕ) : ℚ) / n := by
        ring_nf
      rw [hsimp]
      positivity
  · split
    · rename_i hsq
      have hmul : (1 - (1 - (s : ℚ) / n)) * n = s := by
        have hsimp : (1 : ℚ) - (1 - (s : ℚ) / n) = (s : ℚ) / n := by ring_nf
        rw [hsimp]
        exact div_mul_cancel₀ _ hnQ
      rw [hmul]
      have h2 : ((s : ℚ)) ^ 2 = (k : ℚ) * n := by exact_mod_cast hsq
      exact h2.ge
    · rename_i hsq
      have hmul : (1 - (1 - ((s + 1 : ℕ) : ℚ) / n)) * n = ((s + 1 : ℕ) : ℚ) := by
        have hsimp : (1 : ℚ) - (1 - ((s + 1 : ℕ) : ℚ) / n) = ((s + 1 : ℕ) : ℚ) / n := by
          ring_nf
        rw [hsimp]
        exact div_mul_cancel₀ _ hnQ
      rw [hmul]
      exact_mod_cast (Nat.lt_succ_sqrt' (k * n)).le

/-- The unique-decoding radius is exact and, by the library's real
inequality, always inside the Johnson regime. -/
theorem uniqueDecodingRadiusQ_le_johnsonRadius {k n : ℕ} (hn : 0 < n) :
    ((uniqueDecodingRadiusQ k n : ℚ) : ℝ) ≤ johnsonRadius ((k : ℝ) / n) := by
  have h0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
  have h := uniqueDecodingRadius_le_johnsonRadius h0
  unfold uniqueDecodingRadiusQ johnsonRadius at *
  push_cast at h ⊢
  linarith [h]

-- ----------------------------------------------------------------------------
-- Query counting: least t with (1 − δ)^t ≤ 2^(−bits)
-- ----------------------------------------------------------------------------

/-- Search loop for leastQueries: cur tracks (1 − δ)^t. Returns the
first t (counting from t₀) at which (2^bits)·cur ≤ 1, or none when fuel
runs out. -/
def leastQueriesAux (δ : ℚ) (bits : ℕ) (cur : ℚ) (t : ℕ) (fuel : ℕ) : Option ℕ :=
  if (2 : ℚ) ^ bits * cur ≤ 1 then some t
  else match fuel with
    | 0 => none
    | fuel + 1 => leastQueriesAux δ bits (cur * (1 - δ)) (t + 1) fuel

/-- The loop index only grows. -/
theorem leastQueriesAux_le {δ cur : ℚ} {bits t₀ fuel t : ℕ}
    (h : leastQueriesAux δ bits cur t₀ fuel = some t) : t₀ ≤ t := by
  induction fuel generalizing cur t₀ with
  | zero =>
    unfold leastQueriesAux at h
    split at h
    · exact le_of_eq (Option.some.inj h)
    · simp at h
  | succ f ih =>
    unfold leastQueriesAux at h
    split at h
    · exact le_of_eq (Option.some.inj h)
    · exact (Nat.le_succ t₀).trans (ih h)

/-- Soundness of the loop: a returned t really achieves the bound. -/
theorem leastQueriesAux_sound {δ cur : ℚ} {bits t₀ fuel t : ℕ}
    (h : leastQueriesAux δ bits cur t₀ fuel = some t) :
    (2 : ℚ) ^ bits * (cur * (1 - δ) ^ (t - t₀)) ≤ 1 := by
  induction fuel generalizing cur t₀ with
  | zero =>
    unfold leastQueriesAux at h
    split at h
    · rename_i hc
      have hte : t₀ = t := Option.some.inj h
      subst hte
      simpa using hc
    · simp at h
  | succ f ih =>
    unfold leastQueriesAux at h
    split at h
    · rename_i hc
      have hte : t₀ = t := Option.some.inj h
      subst hte
      simpa using hc
    · have ht := leastQueriesAux_le h
      have h2 := ih h
      have hteq : t - t₀ = (t - (t₀ + 1)) + 1 := by omega
      convert h2 using 2
      rw [hteq, pow_succ']
      ring

/-- Minimality of the loop: no smaller t' ≥ t₀ achieves the bound. -/
theorem leastQueriesAux_min {δ cur : ℚ} {bits t₀ fuel t : ℕ}
    (h : leastQueriesAux δ bits cur t₀ fuel = some t) :
    ∀ t', t₀ ≤ t' → t' < t → ¬ (2 : ℚ) ^ bits * (cur * (1 - δ) ^ (t' - t₀)) ≤ 1 := by
  induction fuel generalizing cur t₀ with
  | zero =>
    intro t' ht0 ht'
    unfold leastQueriesAux at h
    split at h
    · have hte : t₀ = t := Option.some.inj h
      omega
    · simp at h
  | succ f ih =>
    intro t' ht0 ht'
    unfold leastQueriesAux at h
    split at h
    · have hte : t₀ = t := Option.some.inj h
      omega
    · rename_i hc
      rcases eq_or_lt_of_le ht0 with he | hlt
      · subst he
        simpa using hc
      · have h2 := ih h t' (by omega) ht'
        have hteq : t' - t₀ = (t' - (t₀ + 1)) + 1 := by omega
        intro hle
        apply h2
        convert hle using 2
        rw [hteq, pow_succ']
        ring

/-- The least number of independent queries t achieving soundness
(1 − δ)^t ≤ 2^(−bits), found by exact rational search; none if fuel
runs out (raise fuel, or take a larger δ). -/
def leastQueries (δ : ℚ) (bits fuel : ℕ) : Option ℕ :=
  leastQueriesAux δ bits 1 0 fuel

/-- The returned query count achieves the security target. -/
theorem leastQueries_sound {δ : ℚ} {bits fuel t : ℕ}
    (h : leastQueries δ bits fuel = some t) :
    (2 : ℚ) ^ bits * (1 - δ) ^ t ≤ 1 := by
  have h2 := leastQueriesAux_sound h
  simpa using h2

/-- The returned query count is minimal. -/
theorem leastQueries_min {δ : ℚ} {bits fuel t : ℕ}
    (h : leastQueries δ bits fuel = some t) (t' : ℕ) (ht' : t' < t) :
    ¬ (2 : ℚ) ^ bits * (1 - δ) ^ t' ≤ 1 := by
  have h2 := leastQueriesAux_min h t' (Nat.zero_le t') ht'
  simpa using h2

-- ----------------------------------------------------------------------------
-- The assembled report
-- ----------------------------------------------------------------------------

/-- A computed parameter set for one deployment: degree bound k, domain
size n, security target bits. All radii are relative distances (as
fractions of n); query counts are exact rational search results, with
`none` if the fuel cap was hit. johnsonCertified records that the
Johnson row's δ provably sits below the Johnson radius (and hence the
query count there is justified by the proved, literature regime). -/
structure ParameterReport where
  degreeBound : ℕ
  domainSize : ℕ
  securityBits : ℕ
  rate : ℚ
  uniqueDecodingRadius : ℚ
  johnsonRadiusLowerBound : ℚ
  capacity : ℚ
  queriesAtUniqueDecoding : Option ℕ
  queriesAtJohnson : Option ℕ
  queriesAtCapacity : Option ℕ
  johnsonCertified : Bool
  deriving Repr

/-- Compute the parameter report for degree bound k, domain size n,
security target bits, and search fuel. -/
def mkReport (k n bits fuel : ℕ) : ParameterReport where
  degreeBound := k
  domainSize := n
  securityBits := bits
  rate := (k : ℚ) / n
  uniqueDecodingRadius := uniqueDecodingRadiusQ k n
  johnsonRadiusLowerBound := johnsonLower k n
  capacity := capacityQ k n
  queriesAtUniqueDecoding := leastQueries (uniqueDecodingRadiusQ k n) bits fuel
  queriesAtJohnson := leastQueries (johnsonLower k n) bits fuel
  queriesAtCapacity := leastQueries (capacityQ k n) bits fuel
  johnsonCertified := isBelowJohnson (johnsonLower k n) k n

end Parameters

end RsProximity
