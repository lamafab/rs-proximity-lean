import RsProximity.ListDecoding

-- ============================================================================
-- The Crites–Stewart reduction
-- ============================================================================
--
-- Theorem 2: correlated agreement over lines for RS[L, k] implies
-- (δ, l)-list decodability of RS[L, k + 1]. The line construction and the
-- deep-hole bound (Claim 3's algebraic steps) are proved. Theorem 2 itself
-- remains `sorry`: Claim 4 and the final rearrangement are pending.
--
-- Dependencies: ListDecoding -> CritesStewartReduction.
-- Consumer: ResearchDirection imports this module for the capacity-regime
-- conjectures and their list-decoding barrier.
--
-- Reference: Crites–Stewart (ePrint 2025/2046), Section 4.
--
-- Part of the RsProximity library.

namespace RsProximity

open Polynomial

section CritesStewartReduction

variable {F : Type*} [Field F]

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

/-- Correlated agreement at `(δ, ε)` implies list decodability at degree
bound `k + 1`, with the displayed list size. For small enough `ε`, this
is at most `2 * ε * |F|`.

The line construction and deep-hole bound above are proved; Claim 4 and
the final rearrangement remain `sorry`. -/
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

end CritesStewartReduction

end RsProximity
