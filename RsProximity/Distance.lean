import RsProximity.Fold

-- ============================================================================
-- Distance to the Reed-Solomon code
-- ============================================================================
--
-- The two closeness notions the proximity statements are about: a word
-- close to the code on a domain, and a word close to the code on the
-- folded domain, measured by pullback.
--
-- Part of the RsProximity library.

namespace RsProximity

section Distance

variable {F : Type*} [Field F] [CharP F 2]

/-- A word is δ-close to RS[L, k]: it agrees with the table of some
polynomial of natDegree < k on at least a (1 − δ)-fraction of L.

Total over all δ and k; degenerate outside the regime 0 ≤ δ < 1, 1 ≤ k:
- δ ≥ 1, k ≥ 1: every word is close, witnessed by p = 0
- δ < 0, L nonempty: no word is close
- k = 0: the code is empty, so no word is close at any δ

Regime hypotheses live in the theorems, as with β ≠ 0 in the fold. -/
def rsClose [DecidableEq F] (L : Finset F) (k : ℕ) (δ : ℝ) (w : F → F) : Prop :=
  ∃ p : Polynomial F, p.natDegree < k ∧
    ((L.filter fun x => w x = p.eval x).card : ℝ) ≥ (1 - δ) * (L.card : ℝ)

/-- A word on L is δ-close to the code on the folded domain q(L): it
agrees at q(x) with some polynomial p of natDegree < k on at least a
(1 − δ)-fraction of the points x ∈ L. Both sides of the comparison are
constant on the fibers {x, x + β} (foldMap_pair), so the good set is a
union of fibers; equivalently this is rsClose of the folded word on
q(L), pulled back to L to keep the preimage explicit. -/
def rsCloseImage [DecidableEq F] (L : Finset F) (k : ℕ) (δ : ℝ)
    (β : F) (w : F → F) : Prop :=
  ∃ p : Polynomial F, p.natDegree < k ∧
    ((L.filter fun x => w x = p.eval (foldMap β x)).card : ℝ) ≥ (1 - δ) * (L.card : ℝ)

end Distance

end RsProximity
