# RS proximity: correlated agreement for the binary FRI fold

Standalone Lean 4 + Mathlib formalization of the proximity statements behind
binary FRI: what one round of additive folding preserves about a word's
distance to a Reed–Solomon code.

Extracted on 2026-10-10 from the algebra study repository
(`Crypto/ZK/BinaryFRI.lean`), where the same machinery lives inside the full
protocol context (fold chain, Merkle commitments, a worked GF(8) run). The
library is self-contained: every module imports only Mathlib (and other
RsProximity modules), so the folder moves to its own repository as-is.

## File layout

Standard Lean library layout: the package root holds the lakefile and the
root module, and the `RsProximity/` source directory holds the `RsProximity.*`
modules.

```
RsProximity.lean                 root module, re-exports the library
RsProximity/
  Fold.lean                      the additive fold: the map and its kernel,
                                 the base-q decomposition with halved degrees,
                                 the fold on words (all proved)
  Distance.lean                  rsClose, rsCloseImage: closeness of a word to
                                 the RS code, on a domain and on the folded
                                 domain
  CorrelatedAgreement.lean       the deterministic kernel (sorry) and the
                                 bad-challenge corollary (proved from it)
```

## Roadmap

The library is being grown towards the proximity-gap literature, in
particular "Proximity Gaps for Reed–Solomon Codes" (BCIKS20, J. ACM '23,
with the quantitative follow-up ePrint 2025/2055) and "On Reed–Solomon
Proximity Gaps Conjectures" (Crites–Stewart, ePrint 2025/2046):

- `RsProximity/ProximityGap.lean` (planned): the papers' native form of the
  phenomenon: pairs of words f, g and the affine line f + z·g, with
  exceptional-set statements ("all but N challenges z"). Targets: the
  positive results of 2025/2055 (O(1) exceptions at the unique-decoding
  radius, O(n) exceptions with zero proximity loss at the Johnson bound)
  and the barrier beyond (Ω(n^1.99) exceptions required).
- `RsProximity/ListDecoding.lean` (planned): list-size bounds and the
  reduction of Crites–Stewart and 2025/2055: proximity gaps with small
  error imply Reed–Solomon list decoding, which is what blocks progress
  past the Johnson bound.
- `RsProximity/Counterexamples.lean` (planned): the explicit
  counterexamples of Krachun–Kazanin–Haböck (ePrint 2026/782) and
  Diamond–Gruen (ePrint 2025/2010); a larger, construction-heavy
  formalization.
- Mutual correlated agreement (planned section in
  `CorrelatedAgreement.lean`): the batched form whose up-to-capacity
  conjecture (WHIR) was disproved in 2025/2046.

## The setting

A Reed–Solomon code RS[L, k] is the set of evaluation tables on a domain L of
polynomials of degree < k. The **proximity question**: a verifier holds a word
w (an arbitrary table on L) and wants to know whether w is close to *some*
codeword, reading only a few positions. FRI answers it by repeatedly *folding*
the word down to a constant.

Binary fields (characteristic 2) cannot fold by squaring: GF(2ᵏ)ˣ has odd
order, so there is no 2-to-1 multiplicative map. The **additive fold**

```
q(x) = x² + β·x        (β ≠ 0)
```

works instead: it is 𝔽₂-linear (freshman's dream), its kernel is {0, β}, and
q(x + β) = q(x), so it collapses each pair {x, x + β} to one point and halves
a subspace domain. One fold round on a word w solves, on each fiber
{x, x + β} over y = q(x), the 2×2 system

```
w(x)     = p₀(y) + x·p₁(y)
w(x + β) = p₀(y) + (x+β)·p₁(y)
```

and the verifier's challenge c combines the components into the next word's
value `p₀(y) + c·p₁(y)`. For a genuine degree-<2k polynomial this halves the
degree exactly (see `exists_fold_decomp`), so log₂(k) rounds end at a
constant: that is completeness.

## The definitions

- **`rsClose L k δ w`**: w agrees with the evaluation table of some polynomial
  of natDegree < k on at least a (1 − δ)-fraction of L.

- **`rsCloseImage L k δ β w`**: w agrees, at the image point q(x), with some
  polynomial of natDegree < k on at least a (1 − δ)-fraction of the points
  x ∈ L. Both sides of the comparison are constant on the fibers {x, x + β},
  so the good set is a union of fibers.

*Design note.* `rsCloseImage` measures closeness on the folded domain q(L) by
pulling back to L (`w x = p.eval (foldMap β x)`), not by evaluating the fold
at image points as representatives. The naive version
(`rsClose (L.image (foldMap β)) k δ (foldWord β c w)`) inspects the fibers
*of* the image points, which may lie outside L, and the kernel claim below is
false under it: over GF(8) with β = 1, L = {0, 1, α, α+1}, k = 1, δ = 0, the
word w = [0, 0, 0, 1] satisfies both fold hypotheses with P = 0 but is no
line.

## Claim 1: `fold_correlated_agreement` (stated; proof is `sorry`)

The deterministic core of one round:

> If the folds under two **distinct** challenges c ≠ c′ are each δ-close to
> the code on the folded domain (`rsCloseImage`), then w itself is 2δ-close
> to the original code on L (`rsClose`, at degree bound 2k).

*Proof sketch.* The two agreement sets each cover ≥ (1 − δ) of L, so their
intersection covers ≥ (1 − 2δ). On it, the fiber components p₀(y), p₁(y) are
solved as fixed linear combinations of the two nearby codewords (the 2×2
system has determinant c − c′ ≠ 0), hence are codeword-consistent on a large
set, and `p̂₀(q(X)) + X·p̂₁(q(X))` is a degree < 2k witness agreeing with w on
the fibers above that set.

Two properties worth noting:

- **Regime-free.** The argument is pure algebra; it never touches list
  decoding or unique decoding, so it needs no radius hypothesis. Once
  2δ ≥ 1 the conclusion is vacuously true.
- **Tight in what it claims, loose in radius.** The conclusion is at radius
  2δ, not δ. The factor 2 is the price of the elementary proof; eliminating
  it is the hard amplification problem below.

## Claim 2: `fold_bad_challenge_subsingleton` (proved, from Claim 1)

> If w is 2δ-far from RS[L, 2k], then at most one challenge c makes its fold
> δ-close on the folded domain.

Proof: two such challenges would feed Claim 1 and contradict farness. For a
uniform challenge in a finite field this bounds the bad-event probability by
1/|F|. This is the "except with small probability over the challenge" of the
FRI soundness story, at the kernel's factor-2 slack.

## What is fully proved in the file

Everything in §1, no `sorry`:

- `foldMap_eq_zero_iff`, `foldMap_pair`: the fold's kernel is {0, β} and the
  fold is exactly 2-to-1 on pairs {x, x + β}.
- `exists_fold_decomp`: every polynomial decomposes as
  f(X) = p₀(q(X)) + X·p₁(q(X)) with 2·deg pᵢ ≤ deg f (degree halving).
  Uniqueness is not formalized (it is elementary: a composition with a
  degree-2 polynomial has even degree, while X times one has odd degree).
- `foldWord_pair`, `foldWord_eval`: the word fold is well-defined on the
  halved domain, and if w is a polynomial's table, the folded word is the
  table of the folded polynomial p₀ + c·p₁ (the fold reflects the
  decomposition).

The only `sorry` is `fold_correlated_agreement`; Claim 2 is proved from it
and inherits the assumption.

## The amplification gap (literature status)

What FRI actually consumes is stronger than the kernel: the **probabilistic
amplification** at tight radius — "if a non-negligible fraction of challenges
fold w close, then w is close at the *same* radius δ" (equivalently: few bad
challenges, no factor-2 slack). Its status, as of October 2026:

- **Proved**: up to the unique-decoding radius with O(1) exceptional
  challenges and arbitrarily small proximity loss, and up to the Johnson
  bound with O(n) exceptions and zero proximity loss
  (Ben-Sasson–Carmon–Haböck–Kopparty–Saraf, ePrint 2025/2055; the original
  proximity-gap paper is BCIKS20, J. ACM '23).
- **False in general beyond Johnson**: arbitrarily small proximity loss past
  the Johnson bound requires Ω(n^1.99) exceptional challenges (2025/2055);
  the up-to-capacity conjectures are disproved (Crites–Stewart, ePrint
  2025/2046, including WHIR's mutual correlated agreement; Diamond–Gruen,
  ePrint 2025/2010, with counterexample families whose rates tend to 0);
  explicit counterexamples exist at distance Θ(1/log n) below capacity
  (Krachun–Kazanin–Haböck, ePrint 2026/782, over prime-field multiplicative
  domains).
- **Blocked by list decoding**: proximity gaps past Johnson with small error
  would imply new Reed–Solomon list-decoding bounds (2025/2046, 2025/2055),
  a classical open problem.
- **Open refinements**: constant-rate families (Diamond–Gruen's suggested
  salvage; deployed rates 1/2, 1/4 sit here) and extension-field
  parameterizations (challenges from a large extension field make the
  union bound |list| · n / |E| close; the setting of Binius-style
  systems with challenges from GF(2¹²⁸)).

## Checking

As a standalone package (Mathlib pinned to the same revision and toolchain
as the source repository, `v4.30.0-rc1`):

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans for the pinned revision
lake build           # builds RsProximity
```

Expected output: a single `declaration uses 'sorry'` warning for
`fold_correlated_agreement` and nothing else. For a quick type-check of one
file without building the library, `lake env lean RsProximity/CorrelatedAgreement.lean`
from the package root.
