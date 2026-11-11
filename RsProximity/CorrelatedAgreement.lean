import RsProximity.Fold
import RsProximity.Distance

-- ============================================================================
-- Correlated agreement
-- ============================================================================
--
-- General correlated agreement over affine lines, followed by the soundness
-- claim of FRI made precise for one fold round: folding cannot launder a far
-- word into a near one. The "small probability over the challenge" is then a
-- corollary: the bad challenges form at most a singleton.
--
-- Part of the RsProximity library; extracted on 2026-10-10 from the algebra
-- study repository (Crypto/ZK/BinaryFRI.lean).

namespace RsProximity

open Polynomial

section LineCorrelatedAgreement

variable {F : Type*} [Field F]

/-- The word at challenge `z` on the affine line through `u0` and `u1`. -/
def lineWord (u0 u1 : F → F) (z : F) : F → F :=
  fun x => u0 x + z * u1 x

/-- Two words agree with RS codewords on one shared, sufficiently large
subdomain of `L`. This is the conclusion of correlated agreement for a
fixed pair, before quantifying over all affine lines. -/
def pairCorrelatedAgreement (L : Finset F) (k : ℕ) (δ : ℝ)
    (u0 u1 : F → F) : Prop :=
  ∃ D' : Finset F, ∃ p q : Polynomial F,
    D' ⊆ L ∧ p.natDegree < k ∧ q.natDegree < k ∧
      (1 - δ) * (L.card : ℝ) ≤ (D'.card : ℝ) ∧
      ∀ x ∈ D', u0 x = p.eval x ∧ u1 x = q.eval x

/-- Challenges whose line words are `δ`-close to `RS[L, k]`. -/
noncomputable def closeLineChallenges [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ : ℝ) (u0 u1 : F → F) : Finset F := by
  classical
  exact Finset.univ.filter fun z => rsClose L k δ (lineWord u0 u1 z)

/-- The fraction of challenges whose line words are `δ`-close to
`RS[L, k]`: the finite uniform probability over the challenge field. -/
noncomputable def closeLineFraction [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ : ℝ) (u0 u1 : F → F) : ℝ :=
  ((closeLineChallenges L k δ u0 u1).card : ℝ) / (Fintype.card F : ℝ)

/-- Correlated agreement over lines (paper, Definition 2; BCIKS Theorem
1.4): if more than an `ε`-fraction of the line points are `δ`-close to
`RS[L, k]`, then the two original words have correlated agreement. -/
def lineCorrelatedAgreement [Fintype F] [DecidableEq F] (L : Finset F) (k : ℕ)
    (δ ε : ℝ) : Prop :=
  ∀ u0 u1 : F → F,
    ε < closeLineFraction L k δ u0 u1 →
      pairCorrelatedAgreement L k δ u0 u1

/-- The probability formulation of the close-challenge hypothesis is
equivalent to the count-based formulation used by the list-decoding
reduction. -/
theorem lt_closeLineFraction_iff [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ : ℝ) (u0 u1 : F → F) (ε : ℝ) :
    ε < closeLineFraction L k δ u0 u1 ↔
      ε * (Fintype.card F : ℝ) <
        ((closeLineChallenges L k δ u0 u1).card : ℝ) := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  rw [closeLineFraction, lt_div_iff₀ hq]

/-- The count-based presentation of `lineCorrelatedAgreement`. -/
theorem lineCorrelatedAgreement_iff_count [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ ε : ℝ) :
    lineCorrelatedAgreement L k δ ε ↔
      ∀ u0 u1 : F → F,
        ε * (Fintype.card F : ℝ) <
            ((closeLineChallenges L k δ u0 u1).card : ℝ) →
          pairCorrelatedAgreement L k δ u0 u1 := by
  constructor
  · intro h u0 u1 hε
    exact h u0 u1 ((lt_closeLineFraction_iff L k δ u0 u1 ε).2 hε)
  · intro h u0 u1 hε
    exact h u0 u1 ((lt_closeLineFraction_iff L k δ u0 u1 ε).1 hε)

/-- The forward reading of `lineCorrelatedAgreement`: sufficiently many
close line points give correlated agreement for the original pair. -/
theorem pairCorrelatedAgreement_of_closeLineFraction
    [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ ε : ℝ)
    (h : lineCorrelatedAgreement L k δ ε)
    (u0 u1 : F → F)
    (hP : ε < closeLineFraction L k δ u0 u1) :
    pairCorrelatedAgreement L k δ u0 u1 :=
  h u0 u1 hP

/-- The contrapositive, soundness reading: without correlated agreement,
at most an `ε`-fraction of challenges can produce close line words. -/
theorem closeLineFraction_le_of_not_pairCorrelatedAgreement
    [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ ε : ℝ)
    (h : lineCorrelatedAgreement L k δ ε)
    (u0 u1 : F → F)
    (hca : ¬ pairCorrelatedAgreement L k δ u0 u1) :
    closeLineFraction L k δ u0 u1 ≤ ε := by
  by_contra hP
  exact hca (h u0 u1 (lt_of_not_ge hP))

/-- Correlated agreement is preserved by every affine combination: the
shared codewords `p` and `q` give the line codeword `p + z • q`. -/
theorem rsClose_lineWord_of_pairCorrelatedAgreement
    [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ : ℝ)
    (u0 u1 : F → F)
    (hca : pairCorrelatedAgreement L k δ u0 u1)
    (z : F) :
    rsClose L k δ (lineWord u0 u1 z) := by
  rcases hca with ⟨D', p, q, hD', hp, hq, hcard, hagree⟩
  have hsmul : (z • q).natDegree < k :=
    (natDegree_smul_le z q).trans_lt hq
  have hdeg : (p + z • q).natDegree < k :=
    (natDegree_add_le p (z • q)).trans_lt (max_lt hp hsmul)
  refine ⟨p + z • q, hdeg, ?_⟩
  have hsub : D' ⊆ L.filter fun x =>
      lineWord u0 u1 z x = (p + z • q).eval x := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨hD' hx, ?_⟩
    have hx' := hagree x hx
    simp [lineWord, hx'.1, hx'.2, eval_add, eval_smul, smul_eq_mul]
  exact le_trans hcard (by exact_mod_cast Finset.card_le_card hsub)

/-- Once a pair has correlated agreement, every challenge produces a
close line word. -/
theorem closeLineChallenges_eq_univ_of_pairCorrelatedAgreement
    [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ : ℝ)
    (u0 u1 : F → F)
    (hca : pairCorrelatedAgreement L k δ u0 u1) :
    closeLineChallenges L k δ u0 u1 = Finset.univ := by
  classical
  rw [Finset.eq_univ_iff_forall]
  intro z
  rw [closeLineChallenges, Finset.mem_filter]
  exact ⟨Finset.mem_univ z,
    rsClose_lineWord_of_pairCorrelatedAgreement L k δ u0 u1 hca z⟩

/-- Correlated agreement makes the close-challenge probability one. -/
theorem closeLineFraction_eq_one_of_pairCorrelatedAgreement
    [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ : ℝ)
    (u0 u1 : F → F)
    (hca : pairCorrelatedAgreement L k δ u0 u1) :
    closeLineFraction L k δ u0 u1 = 1 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast ((Fintype.card_pos : 0 < Fintype.card F).ne')
  rw [closeLineFraction,
    closeLineChallenges_eq_univ_of_pairCorrelatedAgreement L k δ u0 u1 hca]
  simp [hq]

/-- The proximity-gap behavior of a line: either few challenges are close,
or every challenge is close. -/
theorem closeLineFraction_le_or_eq_one
    [Fintype F] [DecidableEq F]
    (L : Finset F) (k : ℕ) (δ ε : ℝ)
    (h : lineCorrelatedAgreement L k δ ε)
    (u0 u1 : F → F) :
    closeLineFraction L k δ u0 u1 ≤ ε ∨
      closeLineFraction L k δ u0 u1 = 1 := by
  by_cases hca : pairCorrelatedAgreement L k δ u0 u1
  · exact Or.inr (closeLineFraction_eq_one_of_pairCorrelatedAgreement
      L k δ u0 u1 hca)
  · exact Or.inl (closeLineFraction_le_of_not_pairCorrelatedAgreement
      L k δ ε h u0 u1 hca)

end LineCorrelatedAgreement

section FoldCorrelatedAgreement

variable {F : Type*} [Field F] [CharP F 2]

/-- Correlated agreement, the deterministic core of one round (BCIKS20):
if the folds under two distinct challenges are each δ-close to the code
on the folded domain, the word itself is 2δ-close to the original code.
On the intersection of the two agreement sets the fiber components
p₀(y), p₁(y) are solved as fixed linear combinations of the two nearby
codewords (det c − c′ ≠ 0), so they are codeword-consistent on a large
set, and p̂₀(q(X)) + X·p̂₁(q(X)) witnesses the conclusion on the fibers
above that set.

This two-challenge kernel is elementary and regime-free (vacuous once
2δ ≥ 1). The regime-dependence lives in the probabilistic amplification
FRI needs ("enough challenges fold close implies the word is close at
tight radius"): proved up to the unique-decoding radius with O(1)
exceptions and up to the Johnson bound with O(n) exceptions and zero
proximity loss (Ben-Sasson, Carmon, Haböck, Kopparty, Saraf, ePrint
2025/2055). Past Johnson the picture is negative: Ω(n^1.99) exceptions
required (2025/2055), the up-to-capacity conjectures disproved
(Crites-Stewart, ePrint 2025/2046; Diamond-Gruen, ePrint 2025/2010),
explicit counterexamples at Θ(1/log n) below capacity (Krachun,
Kazanin, Haböck, ePrint 2026/782), and positive results past Johnson
would imply new RS list-decoding bounds (2025/2046, 2025/2055).
Refinements by constant rate and extension field are open. -/
theorem fold_correlated_agreement
    [DecidableEq F]
    (β : F) (hβ : β ≠ 0) (L : Finset F) (hL : ∀ x ∈ L, x + β ∈ L)
    (k : ℕ) (δ : ℝ) (w : F → F) (c c' : F) (hcc : c ≠ c')
    (hc : rsCloseImage L k δ β (foldWord β c w))
    (hc' : rsCloseImage L k δ β (foldWord β c' w)) :
    rsClose L (2 * k) (2 * δ) w := sorry

/-- If w is not within 2δ of the code RS[L, 2k], at most one challenge brings
the fold within δ. For a uniform challenge in a finite field this bounds the
bad-event probability by 1/|F|. -/
theorem fold_bad_challenge_subsingleton
    [DecidableEq F]
    (β : F) (hβ : β ≠ 0) (L : Finset F) (hL : ∀ x ∈ L, x + β ∈ L)
    (k : ℕ) (δ : ℝ) (w : F → F)
    (hfar : ¬ rsClose L (2 * k) (2 * δ) w) :
    {c : F | rsCloseImage L k δ β (foldWord β c w)}.Subsingleton := by
  intro c hc c' hc'
  by_contra hne
  exact hfar (fold_correlated_agreement β hβ L hL k δ w c c' hne hc hc')

end FoldCorrelatedAgreement

end RsProximity
