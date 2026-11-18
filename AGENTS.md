# AGENTS.md

## Project purpose

Exploratory Lean 4/Mathlib formalizations of Reed–Solomon proximity gaps,
list decoding, correlated agreement, and related proof-system results.
The repository is research software, not a production cryptographic library.
Mathematical precision and explicit proof status matter more than API stability.

## Toolchain

- Lean: `leanprover/lean4:v4.30.0-rc1`
- Mathlib: `v4.30.0-rc1`
- Lake configuration: `lakefile.toml`
- `autoImplicit` and `relaxedAutoImplicit` are disabled.

Do not edit generated files under `.lake/`.

## Module layout

Dependency graph:

```text
Fold
  → Distance
    → CorrelatedAgreement
      → AffineCombiners
      → ListDecoding
        → CritesStewartReduction
          → ResearchDirection
        → Parameters
```

Responsibilities:

- `Fold.lean`: characteristic-2 folding, canonical base-`foldQ`
  decomposition, and fold-word consistency.
- `Distance.lean`: Reed–Solomon proximity and folded-image definitions.
- `CorrelatedAgreement.lean`: scalar-line correlated agreement,
  close-challenge probabilities, and fold-specific correlated agreement.
- `AffineCombiners.lean`: affine/scalar MCA, witnesses, exceptional
  challenges, and the affine-combiner paper's core bounds.
- `ListDecoding.lean`: list decodability, unique decoding, Johnson-radius
  facts, capacity obstruction, and Johnson-regime correlated agreement.
- `CritesStewartReduction.lean`: quotient-line construction, deep-hole
  lemmas, and the correlated-agreement-to-list-decoding reduction.
- `ResearchDirection.lean`: open capacity-regime conjectures.
- `Parameters.lean`: computable rational radii and query-count certificates.
- `Example/`: executable examples and demos.
- `RsProximity.lean`: root module importing the complete library.

Preserve this dependency direction when moving declarations. Add new library
modules to `RsProximity.lean` and update module-header consumer notes.

## Mathematical conventions

- Use `k` as the strict degree bound: `natDegree p < k`.
  The corresponding code dimension/rate is `k/n`.
- The affine-combiner paper uses maximum degree `d = k - 1`.
  Its degree fraction is therefore `ρ = (k - 1)/n`, not `k/n`.
- Usually `n = L.card` and `q = Fintype.card F`.
- `δ` is relative Hamming distance; agreement is `(1 - δ)n`.
- Characteristic-2 folding assumes `β ≠ 0` and closure under `x ↦ x + β`.
- Lowercase `f, g` usually denote received words/functions; `P, p, q`
  denote polynomials. Paper notation `F, G` corresponds to Lean witnesses
  `p, q`.
- Correlated agreement gives one shared structure. MCA additionally
  quantifies over every candidate reaching `A`; witnesses are then
  existentially quantified separately for each candidate.
- Do not confuse generic `lineWord` combination with the canonical
  decomposition supplied by `exists_fold_decomp` and `fold_decomp_unique`.

## Proof policy

- Fully prove elementary/helper lemmas added to the development.
- `sorry` is acceptable only for clearly identified literature theorems
  awaiting formalization or open conjectures.
- Every `sorry` needs a concise comment giving its source and what remains.
  Do not present these declarations as completed proofs.
- Keep open conjectures in `ResearchDirection.lean`.
- Do not add axioms or untrusted shortcuts to bypass mathematical goals.
- Preserve theorem statements and declaration names during organizational
  refactors unless a semantic change is explicitly requested.
- Existing `sorry` warnings are expected; inspect any new warning or error.

## Verification

For focused Lean changes:

```bash
lake env lean RsProximity/ModuleName.lean
```

For a new or renamed module, its direct target can also be built:

```bash
lake build RsProximity.ModuleName
```

Before finishing implementation work, run:

```bash
lake build
git diff --check
```

The default build includes the library and demos. Do not claim success on the
basis of editing alone.

## Documentation

- `README.md` is the concise project overview and infograph index.
- `THEOREMS.md` is the central theorem/proof-status index.
- Update `THEOREMS.md` when adding, renaming, moving, or proving a main theorem.
- Keep routine lemmas out of `THEOREMS.md`; document them near their Lean
  declarations.
- Keep comments compact, direct, and mathematically explicit.
- Update module headers and this file when changing module responsibilities
  or dependencies.
- Cite the papers in `assets/` precisely; distinguish proved results,
  literature statements, and open conjectures.
- Do not duplicate detailed mathematical exposition across README, module
  headers, and `THEOREMS.md`.

## Working style

- Make minimal, focused changes and preserve existing notation.
- Check downstream imports before moving public declarations.
- Avoid unrelated proof rewrites during file reorganizations.
- Do not commit, push, or otherwise mutate Git history unless explicitly asked.
- Preserve unrelated uncommitted work in the working tree.
