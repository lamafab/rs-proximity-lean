import RsProximity.Distance
import Mathlib.Data.Real.Sqrt

-- ============================================================================
-- List decodability of the Reed-Solomon code
-- ============================================================================
--
-- (δ, l)-list decodability (Elias): around every word, at most l codewords
-- lie within relative Hamming distance δ. Contents: the definition and the
-- unique-decoding regime (l = 1, half the minimum distance), the Johnson
-- radius 1 − √ρ with behavior lemmas and two literature theorems (sorry),
-- the capacity wall (above 1 − ρ no small list exists, sorry), and the
-- Crites–Stewart reduction: correlated agreement over lines implies list
-- decodability of the rate one step up.
--
-- References (paper = Crites–Stewart, ePrint 2025/2046; canonical text at
-- assets/On-RS-Proximity-Gaps-Conjectures.txt, proofs there):
--   rsListDecodable                            paper Definition 1
--   lineCorrelatedAgreement                    paper Definition 2, lines case
--   lineCorrelatedAgreement_upTo_johnsonRadius [BCI+23] Theorem 1.4
--   rsListDecodable_of_lineCorrelatedAgreement paper Theorem 2
--   rsClose_linePoint, linePoint_injective     paper Section 4, Claim 3
--   rsClose_smul_inv_sub_bound                 paper Section 4, deep-hole step
--   rsListDecodable_upTo_johnsonRadius         Johnson 1962;
--                                              Guruswami–Sudan 1998
--   not_rsListDecodable_above_capacity         list decoding capacity
--                                              (counting bound, Elias)
--
-- Part of the RsProximity library.

namespace RsProximity

open Polynomial

section ListDecoding

variable {F : Type*} [Field F]

/-- RS[L, k] is (δ, l)-list decodable (paper, Definition 1): around every
word u, at most l codewords lie within relative Hamming distance δ,
i.e. agree with u on ≥ (1−δ)·|L| points. The close codewords are covered
by a Finset of size ≤ l rather than counted (Set.ncard is 0 on infinite
sets), and counted as polynomials, which agrees with counting tables for
k ≤ |L|. -/
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
-- Below half the minimum distance d = n − k + 1, every Hamming ball
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
-- The relative distance μ = d/n is the minimum distance over the block
-- length, a fixed attribute of the code, not the radius δ. For RS,
-- μ = d/n = (n − k + 1)/n = 1 − k/n + 1/n = 1 − ρ + 1/n.
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
-- The capacity wall: above 1 − ρ, no small list
-- ----------------------------------------------------------------------------
-- Past the list-decoding capacity δ = 1 − ρ the worst-case list size is
-- exponential in n, by pure counting: the statement below is the exact
-- pigeonhole bound, so it doubles as the contrapositive interface to the
-- Johnson and Crites–Stewart list bounds above.

/-- List-decoding capacity of RS codes (the counting/packing bound): above
δ = 1 − ρ = 1 − k/n no small list suffices, i.e. RS[L, k] is not
(δ, l)-list decodable once l is below the pigeonhole bound. Counting
argument: with q = |F|, n = |L|, d = ⌊δn⌋, there are q^k codewords
(polynomials of natDegree < k); each radius-d Hamming ball around a
codeword contains ≥ (n choose d)·(q−1)^d words on L; summing over
codewords and averaging over the words on L (the q − n coordinates
outside L cancel in the average) yields a word whose δ-ball contains
≥ q^{k−n}·(n choose d)·(q−1)^d codewords. For δ = 1 − ρ + ε this grows
like q^{εn}: exponential in n, for every code of rate ρ. This is why
the hypothesis hδ in rsListDecodable_of_lineCorrelatedAgreement
(δ below the capacity of RS[L, k+1]) cannot be removed. Literature
theorem (Elias; standard, cf. Guruswami's list-decoding text); sorry,
formalization pending. -/
theorem not_rsListDecodable_above_capacity [Fintype F] [DecidableEq F]
    (L : Finset F) (hL : 0 < L.card) (k : ℕ) (hk : 0 < k) (δ : ℝ) (l : ℕ)
    (hδ : 1 - (k : ℝ) / L.card < δ)
    (hl : (l : ℝ) * (Fintype.card F : ℝ) ^ L.card <
      (Fintype.card F : ℝ) ^ k * (L.card.choose ⌊δ * (L.card : ℝ)⌋₊ : ℝ) *
        ((Fintype.card F : ℝ) - 1) ^ ⌊δ * (L.card : ℝ)⌋₊) :
    ¬ rsListDecodable L k δ l := sorry

-- ----------------------------------------------------------------------------
-- The Crites–Stewart reduction (paper, Section 4)
-- ----------------------------------------------------------------------------
-- Theorem 2: correlated agreement over lines for RS[L, k] implies
-- (δ, l)-list decodability of RS[L, k + 1]. Proved below: the line
-- construction and the deep-hole bound (Claim 3's algebraic steps).
-- Stated with sorry: Theorem 2 itself (Claim 4 and the final
-- rearrangement pending).

/-- The line point at λ on the Crites–Stewart line:
w_λ(x) = (u(x) − λ)/(x − a) (paper, Section 4, proof of Claim 3).
Meaningful for a ∉ L, so no division by zero occurs. -/
def linePoint (u : F → F) (a l : F) : F → F := fun x => (u x - l) / (x - a)

/-- Claim 3, the per-codeword step: if u is δ-close to RS[L, k+1] via p
and a ∉ L, then the line point at λ = p(a) is δ-close to RS[L, k],
witnessed by the remainder quotient q(X) = (p(X) − p(a))/(X − a): the
agreement set is preserved verbatim and δ is unchanged. -/
theorem rsClose_linePoint [DecidableEq F] (L : Finset F) (k : ℕ) (hk : 0 < k)
    (δ : ℝ) (a : F) (ha : a ∉ L) (u : F → F) (p : Polynomial F)
    (hp : p.natDegree < k + 1)
    (hpδ : ((L.filter fun x => u x = p.eval x).card : ℝ) ≥ (1 - δ) * (L.card : ℝ)) :
    rsClose L k δ (linePoint u a (p.eval a)) := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (p := p) (a := a)
  have hqdeg : q.natDegree < k := by
    rcases eq_or_ne q 0 with hq0 | hq0
    · rw [hq0, natDegree_zero]
      exact hk
    · have hnm : ((X - C a) * q).natDegree = 1 + q.natDegree := by
        rw [natDegree_mul (X_sub_C_ne_zero a) hq0, natDegree_X_sub_C]
      have hle : (p - C (p.eval a)).natDegree ≤ p.natDegree :=
        (natDegree_sub_le p (C (p.eval a))).trans
          (max_le (le_refl _) ((natDegree_C _).le.trans (Nat.zero_le _)))
      have h1 : 1 + q.natDegree ≤ p.natDegree := by
        rw [← hnm, ← hq]
        exact hle
      omega
  refine ⟨q, hqdeg, le_trans hpδ ?_⟩
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  obtain ⟨hxL, hxu⟩ := hx
  have hxa : x - a ≠ 0 := fun h0 => ha ((sub_eq_zero.mp h0) ▸ hxL)
  have hev : p.eval x - p.eval a = (x - a) * q.eval x := by
    have h2 := congrArg (eval x) hq
    simpa only [eval_sub, eval_C, eval_mul, eval_X] using h2
  refine ⟨hxL, ?_⟩
  show (u x - p.eval a) / (x - a) = q.eval x
  rw [hxu, hev]
  exact mul_div_cancel_left₀ (q.eval x) hxa

/-- Distinct λ give distinct line points (on a nonempty domain), so many
distinct p^(j)(a) values yield many distinct close words on the line. -/
theorem linePoint_injective (L : Finset F) (hL : L.Nonempty) (a : F) (ha : a ∉ L)
    (u : F → F) : Function.Injective (linePoint u a) := by
  intro l1 l2 h
  obtain ⟨x0, hx0⟩ := hL
  have hx0a : x0 - a ≠ 0 := fun h0 => ha ((sub_eq_zero.mp h0) ▸ hx0)
  have h2 := congrFun h x0
  simp only [linePoint] at h2
  have h3 : u x0 - l1 = u x0 - l2 := by
    rw [div_eq_iff hx0a, div_mul_cancel₀ _ hx0a] at h2
    exact h2
  exact sub_right_inj.mp h3

/-- The line direction is a deep hole (the paper's step
∆(u(1), RS(Fq, D, k)) ≥ n − k in Claim 3, there c = −1): c·(x − a)⁻¹ with
c ≠ 0 is at distance ≥ |L| − k from RS[L, k], since agreement with p at x
makes x a root of the nonzero polynomial (X − a)·p − c of degree ≤ k. -/
theorem rsClose_smul_inv_sub_bound [DecidableEq F] (L : Finset F) (k : ℕ) (δ : ℝ)
    (a : F) (c : F) (hc : c ≠ 0) (ha : a ∉ L)
    (h : rsClose L k δ (fun x => c * (x - a)⁻¹)) :
    (1 - δ) * (L.card : ℝ) ≤ k := by
  obtain ⟨p, hp, hpδ⟩ := h
  rcases eq_or_ne k 0 with hk0 | hk0
  · subst hk0
    exact absurd hp (Nat.not_lt_zero _)
  set r : Polynomial F := (X - C a) * p - C c with hrdef
  have hra : r.eval a = -c := by
    simp [hrdef]
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, eval_zero] at hra
    exact hc (neg_eq_zero.mp hra.symm)
  have hrdeg : r.natDegree ≤ k := by
    have h1 : ((X - C a) * p).natDegree ≤ 1 + p.natDegree := by
      rcases eq_or_ne p 0 with hp0 | hp0
      · rw [hp0, mul_zero, natDegree_zero]
        omega
      · rw [natDegree_mul (X_sub_C_ne_zero a) hp0, natDegree_X_sub_C]
    have h2 : r.natDegree ≤ max ((X - C a) * p).natDegree (C c).natDegree :=
      natDegree_sub_le ((X - C a) * p) (C c)
    have h3 : (C c : Polynomial F).natDegree ≤ 1 + p.natDegree :=
      (natDegree_C _).le.trans (Nat.zero_le _)
    have h4 : r.natDegree ≤ 1 + p.natDegree := h2.trans (max_le h1 h3)
    omega
  have hroots : (L.filter fun x => r.eval x = 0).card ≤ k := by
    refine (Finset.card_le_card ?_).trans
      ((Multiset.toFinset_card_le _).trans ((card_roots' r).trans hrdeg))
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Multiset.mem_toFinset, mem_roots hr0, IsRoot.def]
    exact hx.2
  have hincl : L.filter (fun x => c * (x - a)⁻¹ = p.eval x) ⊆
      L.filter (fun x => r.eval x = 0) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨hxL, hxu⟩ := hx
    have hxa : x - a ≠ 0 := fun h0 => ha ((sub_eq_zero.mp h0) ▸ hxL)
    refine ⟨hxL, ?_⟩
    have hr_eval : r.eval x = (x - a) * p.eval x - c := by
      simp only [hrdef, eval_sub, eval_mul, eval_X, eval_C]
    rw [hr_eval]
    have h2 : (x - a) * p.eval x = c := by
      have h3 : (x - a) * (c * (x - a)⁻¹) = c := by
        rw [← mul_assoc, mul_comm (x - a) c, mul_assoc, mul_inv_cancel₀ hxa, mul_one]
      rw [hxu] at h3
      exact h3
    rw [h2, sub_self]
  calc (1 - δ) * (L.card : ℝ)
      ≤ ((L.filter fun x => c * (x - a)⁻¹ = p.eval x).card : ℝ) := hpδ
    _ ≤ ((L.filter fun x => r.eval x = 0).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hincl)
    _ ≤ k := Nat.cast_le.mpr hroots

/-- BCIKS Theorem 1.4, sharpened by ePrint 2025/2055: correlated
agreement over lines holds up to the Johnson bound, with error
polynomial in n over q. Literature theorem; sorry, formalization
pending. -/
theorem lineCorrelatedAgreement_upTo_johnsonRadius [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ : ℝ)
    (hδ : δ < johnsonRadius ((k : ℝ) / L.card)) :
    ∃ c : ℕ, lineCorrelatedAgreement L k δ
      (((L.card : ℝ) ^ c) / Fintype.card F) := sorry

/-- Crites–Stewart, Theorem 2: correlated agreement over lines for
RS[L, k] at radius δ with error ε implies (δ, l)-list decodability of
RS[L, k + 1], with l = ⌈εq(q−n)/(q−n−kεq)⌉ where q = |F| and n = |L|.
(For ε < (q−n)/(2kq) this is l ≤ 2εq.)

Sorry: stated, proof pending. Sketch (paper, Section 4): l+1 close
codewords of RS[L, k+1] and Claim 4 give ≥ l(q−n)/(q−n+lk) distinct
close line points via rsClose_linePoint and linePoint_injective (proved);
the choice of l makes this exceed εq, so hgap applies to the line with
u0 = u/(x − a), u1 = −(x − a)⁻¹; its conclusion makes u1 δ-close,
contradicting the deep-hole bound rsClose_smul_inv_sub_bound (proved). -/
theorem rsListDecodable_of_lineCorrelatedAgreement [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (hk : 0 < k) (δ ε : ℝ)
    (hδ0 : 0 ≤ δ)
    (hδ : δ < ((L.card : ℝ) - k - 1) / L.card)
    (hqn : (L.card : ℝ) < Fintype.card F)
    (hε0 : 0 < ε)
    (hε : ε < ((Fintype.card F : ℝ) - L.card) / (k * Fintype.card F))
    (hgap : lineCorrelatedAgreement L k δ ε) :
    rsListDecodable L (k + 1) δ
      (Nat.ceil (ε * Fintype.card F * ((Fintype.card F : ℝ) - L.card) /
        ((Fintype.card F : ℝ) - L.card - k * ε * Fintype.card F))) := by
  sorry

end ListDecoding

end RsProximity
