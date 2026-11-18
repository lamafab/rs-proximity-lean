import RsProximity.CorrelatedAgreement
import Mathlib.Data.Real.Sqrt

-- ============================================================================
-- Affine combiners and mutual correlated agreement
-- ============================================================================
--
-- Affine and scalar MCA, exceptional challenges, the main affine error bound,
-- and the lower bounds separating the two combiners.
--
-- An affine combiner forms `f(x) + (α + β*x)g(x)`. A challenge pair is
-- exceptional when some candidate `P` of degree `< k` agrees with this word on
-- at least `A` coordinates, but no suitable witnesses satisfy the global
-- identity `P = F + (α + β*X)G` while agreeing with `f` and `g` on all but `s`
-- of those coordinates. `affineBadChallenges` collects these unexplained
-- agreements: finding a low-degree combination alone is not enough.
--
-- Dependencies: CorrelatedAgreement -> AffineCombiners.
--
-- References: Chiesa, Weissenberg, Yogev, and Zheng, "Affine Combiners for
-- Reed–Solomon Proximity Gaps" (2026), Theorem 1.1 and Propositions 6.1–6.2.
-- The three literature theorems remain `sorry`; the MCA definitions and
-- honest-combiner evaluation lemma are fully formalized.
--
-- Part of the RsProximity library.

namespace RsProximity

open Polynomial

section AffineCombiners

variable {F : Type*} [Field F]

/-- The affine-combiner word `f(x) + (α + βx)g(x)`. -/
def affineWord (f g : F → F) (α β : F) : F → F :=
  fun x => f x + (α + β * x) * g x

/-- Coordinates of `L` where a word agrees with a candidate polynomial. -/
def polyAgreementSet [DecidableEq F] (L : Finset F) (w : F → F)
    (P : Polynomial F) : Finset F :=
  L.filter fun x => w x = P.eval x

/-- The agreement set `S_{α,β}(P)` from the affine-combiner paper. -/
def affineAgreementSet [DecidableEq F] (L : Finset F) (f g : F → F)
    (α β : F) (P : Polynomial F) : Finset F :=
  polyAgreementSet L (affineWord f g α β) P

/-- The scalar-combiner agreement set `S_α(P)`. -/
def scalarAgreementSet [DecidableEq F] (L : Finset F) (f g : F → F)
    (α : F) (P : Polynomial F) : Finset F :=
  polyAgreementSet L (lineWord f g α) P

/-- Evaluating the polynomial behind an affine combination gives `affineWord`. -/
theorem affineWord_eval (p q : Polynomial F) (α β x : F) :
    affineWord (fun y => p.eval y) (fun y => q.eval y) α β x =
      (p + (C α + C β * X) * q).eval x := by
  simp [affineWord, eval_add, eval_mul, eval_C, eval_X]

/-- Admissible affine witnesses for a candidate `P`, with agreement loss at
most `s`. The condition on `X * q` is the strict-bound form of the paper's
`deg q ≤ d - 1`, where `d = k - 1`; it also handles `q = 0`. The identity is a
global polynomial identity, not merely agreement on `L`. -/
def affineAdmissibleWitness [DecidableEq F] (L : Finset F) (k s : ℕ)
    (f g : F → F) (α β : F) (P p q : Polynomial F) : Prop :=
  p.natDegree < k ∧ (X * q).natDegree < k ∧
    P = p + (C α + C β * X) * q ∧
      ((affineAgreementSet L f g α β P).filter fun x =>
        p.eval x ≠ f x ∨ q.eval x ≠ g x).card ≤ s

/-- Admissible scalar witnesses; both inputs have strict degree bound `k`. -/
def scalarAdmissibleWitness [DecidableEq F] (L : Finset F) (k s : ℕ)
    (f g : F → F) (α : F) (P p q : Polynomial F) : Prop :=
  p.natDegree < k ∧ q.natDegree < k ∧
    P = p + C α * q ∧
      ((scalarAgreementSet L f g α P).filter fun x =>
        p.eval x ≠ f x ∨ q.eval x ≠ g x).card ≤ s

/-- MCA for fixed words and challenges: **every** candidate with at least `A`
agreements **must have** witnesses in the original words. Correlated agreement only
gives one shared structure; it does not explain every candidate. -/
def affineMutualCorrelatedAgreement [DecidableEq F]
    (L : Finset F) (k A s : ℕ) (f g : F → F) (α β : F) : Prop :=
  ∀ P : Polynomial F, P.natDegree < k →
    A ≤ (affineAgreementSet L f g α β P).card →
    ∃ p q : Polynomial F,
      affineAdmissibleWitness L k s f g α β P p q

/-- MCA for fixed words and a fixed scalar challenge. This is likewise a
universal statement about candidates, not merely the existence of one shared
agreement domain for `f` and `g`. -/
def scalarMutualCorrelatedAgreement [DecidableEq F]
    (L : Finset F) (k A s : ℕ) (f g : F → F) (α : F) : Prop :=
  ∀ P : Polynomial F, P.natDegree < k →
    A ≤ (scalarAgreementSet L f g α P).card →
    ∃ p q : Polynomial F,
      scalarAdmissibleWitness L k s f g α P p q

/-- Affine challenges where `affineMutualCorrelatedAgreement` fails: some
candidate of degree `< k` has at least `A` agreements but no admissible
witnesses with loss at most `s`. -/
noncomputable def affineBadChallenges [Fintype F] [DecidableEq F]
    (L : Finset F) (k A s : ℕ) (f g : F → F) : Finset (F × F) := by
  classical
  exact Finset.univ.filter fun c =>
    ¬ affineMutualCorrelatedAgreement L k A s f g c.1 c.2

/-- Scalar challenges where `scalarMutualCorrelatedAgreement` fails. -/
noncomputable def scalarBadChallenges [Fintype F] [DecidableEq F]
    (L : Finset F) (k A s : ℕ) (f g : F → F) : Finset F := by
  classical
  exact Finset.univ.filter fun α =>
    ¬ scalarMutualCorrelatedAgreement L k A s f g α

/-- Finite-count form of "affine MCA error at most `ε`": the exceptional
fraction of independently uniform pairs `(α, β)` is at most `ε`. -/
noncomputable def affineMCAErrorBound [Fintype F] [DecidableEq F]
    (L : Finset F) (k A s : ℕ) (ε : ℝ) : Prop :=
  ∀ f g : F → F,
    ((affineBadChallenges L k A s f g).card : ℝ) ≤
      ε * (Fintype.card F : ℝ) ^ 2

/-- Finite-count form of "scalar MCA error at most `ε`". -/
noncomputable def scalarMCAErrorBound [Fintype F] [DecidableEq F]
    (L : Finset F) (k A s : ℕ) (ε : ℝ) : Prop :=
  ∀ f g : F → F,
    ((scalarBadChallenges L k A s f g).card : ℝ) ≤
      ε * (Fintype.card F : ℝ)

/-- Chiesa–Weissenberg–Yogev–Zheng, Theorem 1.1. With one coordinate of
agreement loss, the affine MCA error is bounded by
`4/(ηq) + 2^14 n^2/(ρ^3 η^10 q^2)` at the displayed Johnson-slack threshold.
The paper's maximum degree is `d = k - 1`, so its degree fraction is
`ρ = (k - 1)/n`, not the dimension rate `k/n`. The explicit bound needs only
`q ≥ n`; `q ≥ n²` is used only for the asymptotic `O(1/q)` consequence.
Literature theorem; formal proof pending. -/
theorem affineMCAErrorBound_of_johnson_slack [Fintype F] [DecidableEq F]
    (L : Finset F) (k A : ℕ) (ρ η : ℝ)
    (hk : 2 ≤ k) (hkn : k ≤ L.card)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρ : ρ = ((k : ℝ) - 1) / (L.card : ℝ))
    (hη0 : 0 < η) (hη : η < 1 - Real.sqrt ρ)
    (hA : A = Nat.ceil ((Real.sqrt ρ + η) * (L.card : ℝ)))
    (hη2 : 4 / ρ ≤ (L.card : ℝ) * η ^ 2)
    (hqn : L.card ≤ Fintype.card F) :
    affineMCAErrorBound L k A 1
      (4 / (η * (Fintype.card F : ℝ)) +
        (2 : ℝ) ^ 14 * (L.card : ℝ) ^ 2 /
          (ρ ^ 3 * η ^ 10 * (Fintype.card F : ℝ) ^ 2)) := sorry

/-- Proposition 6.1: scalar combiners have an `Ω(n/q)` worst-case barrier,
even with larger agreement loss. The numerator counts exceptional challenges;
division by `q` gives the probability lower bound in the paper. -/
theorem scalarMCAErrorBound_lower [Fintype F] [DecidableEq F]
    (L : Finset F) (k A s : ℕ) (hA0 : 1 ≤ A) (hAn : A ≤ L.card)
    (hAs : k < A - s) (ε : ℝ)
    (herr : scalarMCAErrorBound L k A s ε) :
    (((1 + Nat.floor (((L.card : ℝ) - (A : ℝ)) / (s + 1)) : ℕ) : ℝ) /
      (Fintype.card F : ℝ)) ≤ ε := sorry

/-- Proposition 6.2: without agreement loss, affine combiners still incur the
displayed worst-case error. Thus the one-coordinate relaxation in Theorem 1.1
is necessary for its small-error guarantee. -/
theorem affineMCAErrorBound_zero_loss_lower [Fintype F] [DecidableEq F]
    (L : Finset F) (k A : ℕ) (hA0 : 1 ≤ A) (hAn : A ≤ L.card)
    (hAk : k < A) (ε : ℝ)
    (herr : affineMCAErrorBound L k A 0 ε) :
    (((L.card : ℝ) - (A : ℝ) + 1) * ((Fintype.card F : ℝ) - 1)) /
      (Fintype.card F : ℝ) ^ 2 ≤ ε := sorry

end AffineCombiners

end RsProximity
