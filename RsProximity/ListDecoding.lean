import RsProximity.CorrelatedAgreement
import Mathlib.Data.Real.Sqrt

-- ============================================================================
-- List decodability of the Reed-Solomon code
-- ============================================================================
--
-- List decodability, decoding radii, and Johnson-regime correlated agreement.
-- Contents: unique decoding, the Johnson radius, the capacity obstruction,
-- and correlated agreement up to the Johnson radius.
--
-- CorrelatedAgreement.lean supplies the general affine-line API; Distance
-- and Fold are available transitively. CritesStewartReduction imports this
-- module for the list-decoding barrier; ResearchDirection uses it transitively.
--
-- References: Crites–Stewart (ePrint 2025/2046), Definition 1; BCI+23,
-- Theorem 1.4; Johnson 1962; Guruswami–Sudan 1998; Elias's list-decoding
-- capacity bound.
--
-- Part of the RsProximity library.

namespace RsProximity

open Polynomial

section ListDecoding

variable {F : Type*} [Field F]

/-- Around every word, at most `l` polynomials of degree `< k` agree with
it on at least `(1 - δ) * |L|` positions. A finset covers all such polynomials,
so the definition remains meaningful over arbitrary fields. -/
def rsListDecodable [DecidableEq F] (L : Finset F) (k : ℕ) (δ : ℝ) (l : ℕ) : Prop :=
  ∀ u : F → F, ∃ ps : Finset (Polynomial F), ps.card ≤ l ∧
    ∀ p : Polynomial F, p.natDegree < k →
      ((L.filter fun x => u x = p.eval x).card : ℝ) ≥ (1 - δ) * (L.card : ℝ) → p ∈ ps

/-- At list size 1 the close codeword is unique: two low-degree
polynomials both δ-close to the same word are equal. -/
theorem rsListDecodable_one_unique [DecidableEq F] (L : Finset F) (k : ℕ) (δ : ℝ)
    (h : rsListDecodable L k δ 1) (u : F → F) (p q : Polynomial F)
    (hp : p.natDegree < k) (hq : q.natDegree < k)
    (hpδ : ((L.filter fun x => u x = p.eval x).card : ℝ) ≥ (1 - δ) * (L.card : ℝ))
    (hqδ : ((L.filter fun x => u x = q.eval x).card : ℝ) ≥ (1 - δ) * (L.card : ℝ)) :
    p = q := by
  obtain ⟨ps, hcard, hmem⟩ := h u
  have hp' : p ∈ ps := hmem p hp hpδ
  have hq' : q ∈ ps := hmem q hq hqδ
  rw [Finset.card_le_one] at hcard
  exact hcard p hp' q hq'

-- ----------------------------------------------------------------------------
-- Unique decoding: half the minimum distance
-- ----------------------------------------------------------------------------
-- Below half the minimum distance d_min = n − k + 1, every Hamming ball
-- contains at most one codeword: two δ-close codewords agree with the
-- word on ≥ (1 − 2δ)·n points, hence with each other, and their
-- difference is a polynomial of degree ≤ k − 1 with that many roots.

/-- Pairwise form: two codewords δ-close to the same word with
2δ·|L| < |L| − k + 1 are equal. -/
theorem eq_of_close_lt_half_dist [DecidableEq F] (L : Finset F) (k : ℕ) (δ : ℝ)
    (u : F → F) (p q : Polynomial F)
    (hp : p.natDegree < k) (hq : q.natDegree < k)
    (hpδ : ((L.filter fun x => u x = p.eval x).card : ℝ) ≥ (1 - δ) * (L.card : ℝ))
    (hqδ : ((L.filter fun x => u x = q.eval x).card : ℝ) ≥ (1 - δ) * (L.card : ℝ))
    (hδ : 2 * δ * (L.card : ℝ) < (L.card : ℝ) - k + 1) :
    p = q := by
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  -- The agreement counts, over ℝ.
  have hinter : (((L.filter fun x => u x = p.eval x) ∩
      (L.filter fun x => u x = q.eval x)).card : ℝ) ≥ (1 - 2 * δ) * (L.card : ℝ) := by
    have hcu := Finset.card_union_add_card_inter
      (L.filter fun x => u x = p.eval x) (L.filter fun x => u x = q.eval x)
    have hunion : ((L.filter fun x => u x = p.eval x) ∪
        (L.filter fun x => u x = q.eval x)).card ≤ L.card :=
      Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    have hcuR : (((L.filter fun x => u x = p.eval x) ∪
        (L.filter fun x => u x = q.eval x)).card : ℝ) +
        ((L.filter fun x => u x = p.eval x) ∩
          (L.filter fun x => u x = q.eval x)).card =
        ((L.filter fun x => u x = p.eval x).card : ℝ) +
          (L.filter fun x => u x = q.eval x).card := by
      exact_mod_cast hcu
    have hunionR : (((L.filter fun x => u x = p.eval x) ∪
        (L.filter fun x => u x = q.eval x)).card : ℝ) ≤ L.card := by
      exact_mod_cast hunion
    linarith
  -- Points where both agree with u are points where p and q agree.
  have hincl : (L.filter fun x => u x = p.eval x) ∩
      (L.filter fun x => u x = q.eval x) ⊆
      L.filter fun x => p.eval x = q.eval x := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    exact ⟨hx.1.1, hx.1.2.symm.trans hx.2.2⟩
  -- The pairwise agreement set of p and q has size at most k − 1.
  have hpq : (L.filter fun x => p.eval x = q.eval x).card ≤ k - 1 := by
    rcases k with _ | k'
    · exact absurd hp (Nat.not_lt_zero _)
    · have hdeg : (p - q).natDegree ≤ k' := by
        have h := natDegree_sub_le p q
        have hpk : p.natDegree ≤ k' := Nat.lt_succ_iff.mp hp
        have hqk : q.natDegree ≤ k' := Nat.lt_succ_iff.mp hq
        omega
      refine (Finset.card_le_card ?_).trans
        ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans hdeg))
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Multiset.mem_toFinset, mem_roots hsub, IsRoot.def, eval_sub]
      exact sub_eq_zero.mpr hx.2
  -- Chain: (1 − 2δ)·n ≤ |A_p ∩ A_q| ≤ |A_pq| ≤ k − 1 contradicts hδ.
  have h1 : (1 - 2 * δ) * (L.card : ℝ) ≤
      ((L.filter fun x => p.eval x = q.eval x).card : ℝ) :=
    le_trans hinter (Nat.cast_le.mpr (Finset.card_le_card hincl))
  have h2 : ((L.filter fun x => p.eval x = q.eval x).card : ℝ) ≤ (k : ℝ) - 1 := by
    rcases k with _ | k'
    · exact absurd hp (Nat.not_lt_zero _)
    · have hpq' : (L.filter fun x => p.eval x = q.eval x).card ≤ k' := by
        simpa using hpq
      have hk : ((k' + 1 : ℕ) : ℝ) - 1 = (k' : ℝ) := by push_cast; ring
      rw [hk]
      exact_mod_cast hpq'
  nlinarith [h1, h2, hδ]

/-- The unique-decoding guarantee: below half the minimum distance, RS
codes are (δ, 1)-list decodable. -/
theorem rsListDecodable_one_of_lt_half_dist [DecidableEq F] (L : Finset F) (k : ℕ)
    (δ : ℝ) (hδ : 2 * δ * (L.card : ℝ) < (L.card : ℝ) - k + 1) :
    rsListDecodable L k δ 1 := by
  classical
  intro u
  by_cases hex : ∃ p : Polynomial F, p.natDegree < k ∧
    ((L.filter fun x => u x = p.eval x).card : ℝ) ≥ (1 - δ) * (L.card : ℝ)
  · obtain ⟨p0, hp0, hp0δ⟩ := hex
    refine ⟨{p0}, by simp, ?_⟩
    intro p hp hpδ
    rw [Finset.mem_singleton]
    exact eq_of_close_lt_half_dist L k δ u p p0 hp hp0 hpδ hp0δ hδ
  · refine ⟨∅, by simp, ?_⟩
    intro p hp hpδ
    exfalso
    exact hex ⟨p, hp, hpδ⟩

/-- The (1 − ρ)/2 form: below the unique-decoding radius, list size 1
suffices. -/
theorem rsListDecodable_one_of_le_uniqueDecodingRadius [DecidableEq F]
    (L : Finset F) (hL : 0 < L.card) (k : ℕ) (δ : ℝ)
    (hδ : δ ≤ (1 - (k : ℝ) / L.card) / 2) :
    rsListDecodable L k δ 1 := by
  apply rsListDecodable_one_of_lt_half_dist
  have hn : (0 : ℝ) < L.card := by exact_mod_cast hL
  have h1 : (1 - (k : ℝ) / (L.card : ℝ)) * (L.card : ℝ) = (L.card : ℝ) - k := by
    field_simp [hn.ne']
  have h2 : 2 * δ * (L.card : ℝ) ≤ (L.card : ℝ) - k := by
    have h3 : 2 * δ ≤ 1 - (k : ℝ) / L.card := by linarith [hδ]
    calc 2 * δ * (L.card : ℝ) ≤ (1 - (k : ℝ) / L.card) * (L.card : ℝ) :=
        mul_le_mul_of_nonneg_right h3 hn.le
      _ = (L.card : ℝ) - k := h1
  linarith [h2]

-- ----------------------------------------------------------------------------
-- The Johnson bound
-- ----------------------------------------------------------------------------
-- TODO: define rate p = k/n separately.
--
-- The largest radius with a proved small-list guarantee: a code of
-- relative distance μ is list decodable up to 1 − √(1 − μ). For RS
-- codes this gives the Johnson radius 1 − √ρ.
--
-- The relative distance μ = d_min/n is the minimum distance over the block
-- length, a fixed attribute of the code, not the radius δ. For RS,
-- μ = d_min/n = (n − k + 1)/n = 1 − k/n + 1/n = 1 − ρ + 1/n.
--
-- The exact RS Johnson radius is (as n grows the 1/n evaporates):
--   1 − √(1 − μ)    with μ = 1 − ρ + 1/n
--   = 1 − √(1 − 1 + ρ − 1/n)
--   = 1 − √(ρ − 1/n)
--
-- Proved below: behavior lemmas. Stated with sorry: the bound itself
-- (Guruswami–Sudan) and correlated agreement up to it (BCIKS).

/-- The Johnson radius 1 − √ρ as a function of the rate ρ. -/
noncomputable def johnsonRadius (ρ : ℝ) : ℝ := 1 - Real.sqrt ρ

/-- At rate 0 the radius is 1. -/
theorem johnsonRadius_zero : johnsonRadius 0 = 1 := by
  simp [johnsonRadius]

/-- At rate 1 the radius is 0. -/
theorem johnsonRadius_one : johnsonRadius 1 = 0 := by
  simp [johnsonRadius]

/-- The radius shrinks as the rate grows. -/
theorem johnsonRadius_antiOn : StrictAntiOn johnsonRadius (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hs : Real.sqrt x < Real.sqrt y := Real.sqrt_lt_sqrt hx.1 hxy
  unfold johnsonRadius
  linarith

/-- (1−ρ)/2 ≤ 1−√ρ, equivalently (1−√ρ)² ≥ 0. -/
theorem uniqueDecodingRadius_le_johnsonRadius {ρ : ℝ} (h0 : 0 ≤ ρ) :
    (1 - ρ) / 2 ≤ johnsonRadius ρ := by
  have hs := Real.sq_sqrt h0
  have h : 2 * Real.sqrt ρ ≤ 1 + ρ := by
    nlinarith [sq_nonneg (1 - Real.sqrt ρ)]
  unfold johnsonRadius
  linarith

/-- 1−√ρ ≤ 1−ρ for 0 ≤ ρ ≤ 1, equivalently √ρ·(1−√ρ) ≥ 0. -/
theorem johnsonRadius_le_capacity {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    johnsonRadius ρ ≤ 1 - ρ := by
  have hs1 : Real.sqrt ρ ≤ 1 := (Real.sqrt_le_sqrt h1).trans_eq Real.sqrt_one
  have hs := Real.sq_sqrt h0
  have hprod : 0 ≤ Real.sqrt ρ * (1 - Real.sqrt ρ) :=
    mul_nonneg (Real.sqrt_nonneg ρ) (sub_nonneg.mpr hs1)
  unfold johnsonRadius
  nlinarith

/-- Rate 1/4 (a common FRI blowup): the Johnson radius is exactly 1/2. -/
theorem johnsonRadius_quarter : johnsonRadius (1/4 : ℝ) = 1/2 := by
  have h : Real.sqrt (1/4 : ℝ) = 1/2 := by
    rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold johnsonRadius
  rw [h]
  norm_num

/-- The Johnson bound for RS codes (Johnson 1962; Guruswami–Sudan 1998):
below the Johnson radius, RS[L, k] is (δ, l)-list decodable with l ≤ n²
(schematic; the precise list size is smaller). Literature theorem; sorry,
formalization pending. -/
theorem rsListDecodable_upTo_johnsonRadius [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ : ℝ)
    (hδ : δ ≤ johnsonRadius ((k : ℝ) / L.card)) :
    rsListDecodable L k δ (L.card ^ 2) := sorry

-- ----------------------------------------------------------------------------
-- The capacity wall: beyond 1 − ρ, no small-list guarantee
-- ----------------------------------------------------------------------------
-- Unique decoding gives at most one candidate, while the Johnson bound
-- gives bounded lists in its regime. Beyond δ = 1 − ρ, the packing bound
-- forces some received word to have exponentially many nearby codewords.
-- The exact finite-field bound below also explains why the capacity
-- hypothesis in the Crites–Stewart reduction cannot simply be removed.

/-- Exact finite-field packing form of the capacity obstruction: if
`1 - k / |L| < δ` and `l` is below the displayed counting bound, then
`RS[L, k]` is not `(δ, l)`-list decodable. The bound follows by averaging
Hamming balls over all received words. Literature theorem (Elias);
formalization pending. -/
theorem not_rsListDecodable_above_capacity [Fintype F] [DecidableEq F]
    (L : Finset F) (hL : 0 < L.card) (k : ℕ) (hk : 0 < k) (δ : ℝ) (l : ℕ)
    (hδ : 1 - (k : ℝ) / L.card < δ)
    (hl : (l : ℝ) * (Fintype.card F : ℝ) ^ L.card <
      (Fintype.card F : ℝ) ^ k * (L.card.choose ⌊δ * (L.card : ℝ)⌋₊ : ℝ) *
        ((Fintype.card F : ℝ) - 1) ^ ⌊δ * (L.card : ℝ)⌋₊) :
    ¬ rsListDecodable L k δ l := sorry

/-- BCIKS Theorem 1.4, sharpened by ePrint 2025/2055: correlated
agreement over lines holds up to the Johnson bound, with error
polynomial in n over q. Literature theorem; sorry, formalization
pending. -/
theorem lineCorrelatedAgreement_upTo_johnsonRadius [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ : ℝ)
    (hδ : δ < johnsonRadius ((k : ℝ) / L.card)) :
    ∃ c : ℕ, lineCorrelatedAgreement L k δ
      (((L.card : ℝ) ^ c) / Fintype.card F) := sorry

end ListDecoding

end RsProximity
