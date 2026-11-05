import Example.GF8
import RsProximity

/-!
# Demo: the binary additive fold over GF(8)

The library's fold (Fold.lean) instantiated on the decidable field G8,
with β = 1: q(x) = x² + x. The demo word is the table of
f(X) = 1 + α·X (degree < 2), whose base-q decomposition
f(X) = p₀(q(X)) + X·p₁(q(X)) has constant components p₀ = 1, p₁ = α.

Demonstrated, all by decide or by instantiating the library theorems:

- the fold is 2-to-1 on GF(8) with kernel {0, 1}, image a 4-element
  subspace;
- the fiber solve (fold_fiber_solve) on the fiber {0, 1} over y = 0
  recovers p₀(0) = 1 and p₁(0) = α from w(0) = 1, w(1) = 1 + α;
- the word fold (foldWord, foldWord_eval) at challenge c = α computes
  p₀(0) + α·p₁(0) = 1 + α·α, matching the folded polynomial at q(0);
- foldWord is constant on fibers (foldWord_pair), so it descends to
  the halved domain.
-/

open G8 RsProximity Polynomial

/-- The demo word: the table of f(X) = 1 + α·X on GF(8). -/
def wdemo : G8 → G8 := fun x => 1 + α * x

/-- The polynomial behind the demo word. Used only in Prop-level
instantiations of the library theorems; Polynomial arithmetic on G8 is
noncomputable, hence the marker. -/
noncomputable def fdemo : Polynomial G8 := C 1 + C α * X

-- The fold q(x) = x² + x is 2-to-1 on GF(8): the image has 4 elements.
example : (Finset.univ.image (foldMap (1 : G8))).card = 4 := by decide

-- The kernel is {0, 1}: the pair {x, x + 1} collapses (foldMap_pair,
-- and foldMap_eq_zero_iff), here verified on all 8 points.
example : ∀ x : G8, foldMap 1 (x + 1) = foldMap 1 x := by decide
example : ∀ x : G8, foldMap 1 x = 0 ↔ x = 0 ∨ x = 1 := by decide

-- The fiber over y = q(0) = 0 is {0, 1}. On it the word reads
-- w(0) = 1 and w(1) = 1 + α, and the fiber-local 2×2 solve recovers
-- the components p₀(0) = 1, p₁(0) = α: the library's fold_fiber_solve
-- instantiated with a := 1, b := α.
example : α = (wdemo 0 + wdemo (0 + 1)) / 1 ∧ 1 = wdemo 0 + 0 * α :=
  fold_fiber_solve (F := G8) 1 one_ne_zero wdemo 0 1 α (by decide) (by decide)

-- The word fold at challenge c = α, computed concretely:
-- p₁(0) = (w(0) + w(1))/1 = α, so the folded value at y = 0 is
-- p₀(0) + α·p₁(0) = 1 + α·α.
example : foldWord 1 α wdemo 0 = 1 + α * α := by decide

-- The folded word is the folded polynomial p₀ + c·p₁ evaluated at
-- q(x): the library's foldWord_eval, instantiated on the demo data.
example (c : G8) :
    foldWord 1 c wdemo 0 = (C 1 + C c * C α).eval (foldMap 1 0) := by
  refine foldWord_eval 1 c one_ne_zero fdemo (C 1) (C α) ?_ wdemo ?_ 0
  · -- f = p₀(q(X)) + X·p₁(q(X)): with constant components this is just
    -- 1 + α·X = 1 + X·α.
    rw [fdemo, C_comp, C_comp]
    ring
  · intro x
    simp [wdemo, fdemo, eval_add, eval_mul, eval_C, eval_X]

-- The folded word is well-defined on the halved image domain: both
-- representatives of a fiber give the same value (foldWord_pair).
example : ∀ x : G8, foldWord 1 α wdemo (x + 1) = foldWord 1 α wdemo x := by decide
