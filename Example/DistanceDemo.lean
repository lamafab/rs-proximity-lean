import RsProximity.ListDecoding

/-!
# Demo: rsClose and rsListDecodable on a tiny concrete code

The constant code on 4 points over ZMod 5: k = 1, so codewords are the
constant tables (c, c, c, c). The running word is w = (3, 3, 3, 5):
the constant 3, corrupted at the point 3.

What this file demonstrates:

- `rsClose_pos`: w is 1/4-close to the code, via the witness p = C 3
  (agreement on 3 of 4 points, and 3/4 = (1 − 1/4));
- `rsClose_zero_fails`: w is not 0-close, i.e. it is not itself a
  codeword: agreement everywhere would force 3 = 5;
- `constCode_listDecodable`: the code is (1/4, 1)-list decodable.
  Around every word u, at most one constant lies within the radius:
  distinct constants have disjoint agreement sets, and two sets of
  size ≥ 3 cannot fit inside 4 points;
- `constCode_close_unique`: the uniqueness corollary in action, via
  the library's rsListDecodable_one_unique.
-/

open RsProximity Polynomial

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The domain: four points of ZMod 5. -/
def L5 : Finset (ZMod 5) := {0, 1, 2, 3}

/-- The running word: the constant 3, corrupted at the point 3. -/
def w5 : ZMod 5 → ZMod 5 := fun x => if x = 3 then 5 else 3

/-- w is 1/4-close to RS[L5, 1]: the constant polynomial 3 agrees with
it on {0, 1, 2}, three of the four points. -/
example : rsClose L5 1 (1/4 : ℝ) w5 := by
  refine ⟨C 3, by rw [natDegree_C]; exact Nat.one_pos, ?_⟩
  have hS : L5.filter (fun x => w5 x = (C 3).eval x) = {0, 1, 2} := by
    simp only [eval_C]
    decide
  have hcard3 : ({0, 1, 2} : Finset (ZMod 5)).card = 3 := by decide
  have hcard : L5.card = 4 := by decide
  rw [hS, hcard3, hcard]
  norm_num

/-- w is not 0-close: it is not a codeword. Agreement on all four
points would make a constant polynomial equal to both 3 and 5. -/
example : ¬ rsClose L5 1 (0 : ℝ) w5 := by
  rintro ⟨p, hp, hcount⟩
  have hpc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hp)
  have hcard : L5.card = 4 := by decide
  have h4 : 4 ≤ (L5.filter fun x => w5 x = p.eval x).card := by
    have hrw : (1 - 0 : ℝ) * (L5.card : ℝ) = 4 := by rw [hcard]; norm_num
    rw [hrw] at hcount
    exact_mod_cast hcount
  have hEq : L5.filter (fun x => w5 x = p.eval x) = L5 :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hcard]; exact h4)
  have h0mem : (0 : ZMod 5) ∈ L5.filter (fun x => w5 x = p.eval x) := by
    rw [hEq]; decide
  have h3mem : (3 : ZMod 5) ∈ L5.filter (fun x => w5 x = p.eval x) := by
    rw [hEq]; decide
  rw [Finset.mem_filter] at h0mem h3mem
  have e0 : w5 0 = 3 := by decide
  have e3 : w5 3 = 5 := by decide
  have h35 : (3 : ZMod 5) = 5 := by
    calc (3 : ZMod 5) = w5 0 := e0.symm
      _ = p.eval 0 := h0mem.2
      _ = p.coeff 0 := by rw [hpc]; simp
      _ = p.eval 3 := by rw [hpc]; simp
      _ = w5 3 := h3mem.2.symm
      _ = 5 := e3
  exact absurd h35 (by decide)

/-- The tiny code is (1/4, 1)-list decodable: around every word u, at
most one codeword sits within radius 1/4. Distinct constants have
disjoint agreement sets, so two constants each agreeing with u on ≥ 3
of the 4 points would need 6 points. -/
theorem constCode_listDecodable : rsListDecodable L5 1 (1/4 : ℝ) 1 := by
  intro u
  have aux : ∀ p : Polynomial (ZMod 5), p.natDegree < 1 →
      ((L5.filter fun x => u x = p.eval x).card : ℝ) ≥ (1 - 1/4) * (L5.card : ℝ) →
      3 ≤ (L5.filter fun x => u x = p.coeff 0).card := by
    intro p hp hpδ
    have hpc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hp)
    have hev : ∀ x : ZMod 5, p.eval x = p.coeff 0 := by
      intro x
      rw [hpc]
      simp
    have hS : (L5.filter fun x => u x = p.eval x) =
        L5.filter (fun x => u x = p.coeff 0) := by
      ext x
      simp only [Finset.mem_filter]
      rw [hev x]
    have hcard : L5.card = 4 := by decide
    have hge : (3 : ℝ) ≤ (L5.filter fun x => u x = p.eval x).card := by
      have hrw : (1 - 1/4 : ℝ) * (L5.card : ℝ) = 3 := by rw [hcard]; norm_num
      rw [hrw] at hpδ
      exact hpδ
    have h3 : 3 ≤ (L5.filter fun x => u x = p.eval x).card := by exact_mod_cast hge
    rwa [hS] at h3
  by_cases h : ∃ c : ZMod 5, 3 ≤ (L5.filter fun x => u x = c).card
  · obtain ⟨c, hc⟩ := h
    refine ⟨{C c}, by simp, ?_⟩
    intro p hp hpδ
    have h3 := aux p hp hpδ
    have hcc : p.coeff 0 = c := by
      by_contra hne
      have hdisj : Disjoint (L5.filter fun x => u x = p.coeff 0)
          (L5.filter fun x => u x = c) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_filter] at hx1 hx2
        exact hne (hx1.2.symm.trans hx2.2)
      have hunion : (L5.filter fun x => u x = p.coeff 0).card +
          (L5.filter fun x => u x = c).card ≤ L5.card := by
        rw [← Finset.card_union_of_disjoint hdisj]
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hmem | hmem <;> rw [Finset.mem_filter] at hmem
        exacts [hmem.1, hmem.1]
      have hcard : L5.card = 4 := by decide
      rw [hcard] at hunion
      omega
    rw [Finset.mem_singleton, eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hp), hcc]
  · push Not at h
    refine ⟨∅, by simp, ?_⟩
    intro p hp hpδ
    have h3 := aux p hp hpδ
    have hlt := h (p.coeff 0)
    omega

/-- Uniqueness in action: two constant codewords both 1/4-close to the
same word are equal, by the library's rsListDecodable_one_unique. -/
example (p q : Polynomial (ZMod 5))
    (hp : p.natDegree < 1) (hq : q.natDegree < 1)
    (hpδ : ((L5.filter fun x => w5 x = p.eval x).card : ℝ) ≥
      (1 - 1/4) * (L5.card : ℝ))
    (hqδ : ((L5.filter fun x => w5 x = q.eval x).card : ℝ) ≥
      (1 - 1/4) * (L5.card : ℝ)) :
    p = q :=
  rsListDecodable_one_unique L5 1 (1/4 : ℝ) constCode_listDecodable w5 p q hp hq hpδ hqδ
