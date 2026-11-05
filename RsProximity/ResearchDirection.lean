import RsProximity.ListDecoding
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- ============================================================================
-- Research directions: the standing conjectures, stated as targets
-- ============================================================================
--
-- The open statements of the proximity-gap area after Crites–Stewart
-- (ePrint 2025/2046), phrased positively, as the theorems one would
-- want to prove. Every proof in this file is `sorry`: these are
-- conjectures, not theorems. The bias here is deliberate: each
-- statement asserts that the repaired form HOLDS, up to the
-- list-decoding capacity bound. Theorem 2
-- (rsListDecodable_of_lineCorrelatedAgreement, ListDecoding.lean)
-- explains why the small-error regimes are expected to be hard:
-- proving them would imply new classical list-decoding results.
--
-- Contents:
--   qAryEntropy: the q-ary entropy function H_q, which sets the
--     list-decoding capacity bound (Elias, Theorem 7.4.1 of the paper).
--   rsListDecodable_upTo_listDecodingCapacity: Our Conjecture 1 of the
--     paper, the repair of DEEP-FRI's Conjecture 2.3 (prime fields;
--     Our Conjecture 4 is the extension-field variant, with H_p).
--   lineCorrelatedAgreement_upTo_listDecodingCapacity: Our Conjecture 2,
--     the repair of BCIKS's Conjecture 8.4 for lines (Our Conjecture 5
--     is the extension-field variant).
--   mutualCorrelatedAgreement and
--   mutualCorrelatedAgreement_upTo_listDecodingCapacity: the ACFY24b
--     definition for the power generator, and Our Conjecture 3 (Our
--     Conjecture 6 is the extension-field variant).
--
-- Not yet stateable with the current machinery: the computational
-- question (hardness of bounded-distance decoding past the Johnson
-- bound on small fields, research direction 1 of the paper) needs
-- complexity theory; the large-error (mutual) correlated agreement
-- direction (research direction 3) is a parameter regime of the same
-- statements below.
--
-- TODO/NOTE: the statements below are the prime-field forms (Our
-- Conjectures 1-3 of the paper). The extension-field variants (Our
-- Conjectures 4-6) are not yet formalized. They differ only in the
-- entropy argument: H_p evaluated at the characteristic p, where
-- q = p^d, instead of H_q. Stating them needs the characteristic in
-- scope, e.g. hypotheses CharP F p, Nat.Prime p, and
-- Fintype.card F = p ^ d. This is the case that matters for binary
-- fields and Binius-style systems, where the domain sits in a small
-- subfield and challenges come from a large extension (Section 5 of
-- the paper, Corollary 2 and Theorem 3 there).
--
-- Part of the RsProximity library.

namespace RsProximity

section ResearchDirections

variable {F : Type*} [Field F]

/-- The q-ary entropy function
H_q(x) = x·log_q(q−1) − x·log_q(x) − (1−x)·log_q(1−x):
the per-coordinate volume exponent (base q) of a Hamming ball of
relative radius x. It sets the list-decoding capacity: codes of rate ρ
have exponential lists beyond the δ with H_q(δ) = 1 − ρ (Elias;
Theorem 7.4.1 of the paper). For large q, H_q(x) ≈ x, recovering the
"up to capacity" range δ < 1 − ρ; for small q the loss is about
1/log_2(q) (Claim 1 of the paper). -/
noncomputable def qAryEntropy (q : ℕ) (x : ℝ) : ℝ :=
  x * Real.logb (q : ℝ) ((q : ℝ) - 1) - x * Real.logb (q : ℝ) x -
    (1 - x) * Real.logb (q : ℝ) (1 - x)

/-- Our Conjecture 1 of Crites–Stewart, the repair of DEEP-FRI's
Conjecture 2.3: Reed–Solomon codes over prime fields are list decodable
up to list-decoding capacity with polynomial list size. For every rate
there is an exponent c such that every RS code of that rate with
H_q(δ) ≤ 1 − ρ − η is (δ, l)-list decodable with l ≤ (n/η)^c.
Stated per code; the conjecture's content is that c depends only on
the rate. The extension-field variant (Our Conjecture 4) replaces
H_q by H_p. -/
theorem rsListDecodable_upTo_listDecodingCapacity [Fintype F] [DecidableEq F]
    [Fact (Nat.Prime (Fintype.card F))]
    (L : Finset F) (k : ℕ) (δ η : ℝ)
    (hη : 0 < η) (hδ0 : 0 ≤ δ)
    (hδ : qAryEntropy (Fintype.card F) δ ≤ 1 - (k : ℝ) / L.card - η) :
    ∃ c l : ℕ, rsListDecodable L k δ l ∧ (l : ℝ) ≤ ((L.card : ℝ) / η) ^ c := by
  sorry

/-- Our Conjecture 2 of Crites–Stewart, the repair of BCIKS's
Conjecture 8.4 for lines: correlated agreement over lines holds up to
list-decoding capacity, δ ≤ 1 − H_q(δ) − 1/n − η, with error
ε = n^c₂ / ((ηρ)^c₁ · q) for some constants c₁, c₂. The extension-field
variant (Our Conjecture 5) replaces H_q by H_p. -/
theorem lineCorrelatedAgreement_upTo_listDecodingCapacity [Fintype F]
    [DecidableEq F] [Fact (Nat.Prime (Fintype.card F))]
    (L : Finset F) (hL : 0 < L.card) (k : ℕ) (δ η : ℝ)
    (hη : 0 < η) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - qAryEntropy (Fintype.card F) δ - 1 / (L.card : ℝ) - η) :
    ∃ c1 c2 : ℕ, lineCorrelatedAgreement L k δ
      ((L.card : ℝ) ^ c2 / ((η * (k : ℝ) / L.card) ^ c1 * Fintype.card F)) := by
  sorry

open Classical in
/-- Mutual correlated agreement for the power generator
Gen(ℓ; α) = (1, α, ..., α^{ℓ−1}), α uniform in F: Definition 7 of the
paper (from ACFY24b), specialized to that generator. The batched
combination Σⱼ αʲ·f_j may agree with a codeword on a large set S only
if EVERY constituent f_i agrees with some codeword on the same S: the
failure event (the combination is explained on S, but some f_i is not)
has probability ≤ err. This is the batched strengthening of correlated
agreement used by WHIR's soundness analysis. -/
def mutualCorrelatedAgreement [Fintype F] [DecidableEq F] (L : Finset F) (k : ℕ)
    (l : ℕ) (δ err : ℝ) : Prop :=
  ∀ f : Fin l → F → F,
    ((Finset.univ.filter fun α =>
        ∃ S : Finset F, S ⊆ L ∧ (1 - δ) * (L.card : ℝ) ≤ (S.card : ℝ) ∧
          (∃ v : Polynomial F, v.natDegree < k ∧
            ∀ x ∈ S, v.eval x = ∑ j : Fin l, α ^ (j : ℕ) * f j x) ∧
          (∃ i : Fin l, ∀ v' : Polynomial F, v'.natDegree < k →
            ∃ x ∈ S, v'.eval x ≠ f i x)).card : ℝ)
      ≤ err * (Fintype.card F : ℝ)

/-- Our Conjecture 3 of Crites–Stewart, the repair of WHIR's
Conjecture 4.12: mutual correlated agreement for the power generator
holds up to list-decoding capacity, 0 < H_q(δ) < 1 − 1/n − ρ − η, with
error of the schematic form (ℓ·n)^c₂ / ((ηρ)^c₁ · q) for some constants
c₁, c₂ (the paper's form has further constant factors; the existentials
absorb them). The extension-field variant (Our Conjecture 6) replaces
H_q by H_p. -/
theorem mutualCorrelatedAgreement_upTo_listDecodingCapacity [Fintype F]
    [DecidableEq F] [Fact (Nat.Prime (Fintype.card F))]
    (L : Finset F) (hL : 0 < L.card) (k l : ℕ) (δ η : ℝ)
    (hη : 0 < η)
    (hδ0 : 0 < qAryEntropy (Fintype.card F) δ)
    (hδ : qAryEntropy (Fintype.card F) δ <
      1 - 1 / (L.card : ℝ) - (k : ℝ) / L.card - η) :
    ∃ c1 c2 : ℕ, mutualCorrelatedAgreement L k l δ
      (((l : ℝ) * L.card) ^ c2 /
        ((η * (k : ℝ) / L.card) ^ c1 * Fintype.card F)) := by
  sorry

end ResearchDirections

end RsProximity
