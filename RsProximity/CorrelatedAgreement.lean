import RsProximity.Fold
import RsProximity.Distance

-- ============================================================================
-- Correlated agreement
-- ============================================================================
--
-- The soundness claim of FRI, made precise for one fold round: folding
-- cannot launder a far word into a near one. The "small probability over
-- the challenge" is then a corollary: the bad challenges form at most a
-- singleton.
--
-- Part of the RsProximity library; extracted on 2026-10-10 from the algebra
-- study repository (Crypto/ZK/BinaryFRI.lean).

namespace RsProximity

section CorrelatedAgreement

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

/-- The "except with small probability over the challenge" of the
soundness story: if w is 2δ-far from RS[L, 2k], at most one challenge
folds it δ-close. For a uniform challenge in a finite field this bounds
the bad-event probability by 1/|F|. -/
theorem fold_bad_challenge_subsingleton
    [DecidableEq F]
    (β : F) (hβ : β ≠ 0) (L : Finset F) (hL : ∀ x ∈ L, x + β ∈ L)
    (k : ℕ) (δ : ℝ) (w : F → F)
    (hfar : ¬ rsClose L (2 * k) (2 * δ) w) :
    {c : F | rsCloseImage L k δ β (foldWord β c w)}.Subsingleton := by
  intro c hc c' hc'
  by_contra hne
  exact hfar (fold_correlated_agreement β hβ L hL k δ w c c' hne hc hc')

end CorrelatedAgreement

end RsProximity
