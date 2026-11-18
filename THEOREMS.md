# Theorems

Only the main results are listed here; helper lemmas and routine API results are documented in the source. **Proved** declarations have Lean proofs, while **`sorry`** marks a literature theorem awaiting formalization or an open conjecture.

| Area / module | Theorem | Status | Main statement |
| --- | --- | --- | --- |
| **Folding — `Fold.lean`** | `exists_fold_decomp` | Proved | Every polynomial has a base-`foldQ` decomposition into two components with appropriately halved degrees. |
| | `foldWord_eval` | Proved | Folding a polynomial's evaluation table agrees with evaluating the folded polynomial `p₀ + c * p₁`. |
| **Correlated agreement — `CorrelatedAgreement.lean`** | `closeLineFraction_le_or_eq_one` | Proved | Assuming line correlated agreement, the close-challenge fraction is either at most `ε` or exactly 1. |
| | `fold_correlated_agreement` | **`sorry`** | Two distinct close folds imply that the original word is `2δ`-close to `RS[L, 2k]`. |
| **List decoding — `ListDecoding.lean`** | `rsListDecodable_one_of_le_uniqueDecodingRadius` | Proved | Reed–Solomon codes are uniquely decodable at radius at most `(1 - k/n) / 2`. |
| | `rsListDecodable_upTo_johnsonRadius` | **`sorry`** | States the Johnson/Guruswami–Sudan list-decoding bound. |
| | `lineCorrelatedAgreement_upTo_johnsonRadius` | **`sorry`** | States correlated agreement over affine lines up to the Johnson radius, with error `n^c / \|F\|`. |
| | `not_rsListDecodable_above_capacity` | **`sorry`** | States the finite-field packing obstruction to small list sizes above the capacity radius. |
| **Crites–Stewart reduction — `CritesStewartReduction.lean`** | `rsListDecodable_of_lineCorrelatedAgreement` | **`sorry`** | States the Crites–Stewart reduction from line correlated agreement at degree `k` to list decodability at degree `k + 1`, with an explicit list-size bound. |
| **Affine combiners and mutual correlated agreement — `AffineCombiners.lean`** | `affineMCAErrorBound_of_johnson_slack` | **`sorry`** | With `s = 1` and `ρ = (k - 1)/n`, bounds affine MCA error by `4/(ηq) + 2^14 n^2/(ρ^3 η^10 q^2)` at the Johnson-slack threshold. |
| | `scalarMCAErrorBound_lower` | **`sorry`** | Gives the scalar-combiner lower bound `(1 + floor((n - A)/(s + 1)))/q`, establishing the worst-case `Ω(n/q)` barrier. |
| | `affineMCAErrorBound_zero_loss_lower` | **`sorry`** | With `s = 0`, gives the lower bound `(n - A + 1)(q - 1)/q^2`, showing why the main guarantee needs one coordinate of agreement loss. |
| **Research directions — `ResearchDirection.lean`** | `rsListDecodable_upTo_listDecodingCapacity` | **`sorry` — open conjecture** | List decoding extends up to capacity with polynomially bounded lists. |
| | `lineCorrelatedAgreement_upTo_listDecodingCapacity` | **`sorry` — open conjecture** | Line correlated agreement extends up to capacity with the displayed error bound. |
| | `mutualCorrelatedAgreement_upTo_listDecodingCapacity` | **`sorry` — open conjecture** | Power-generator batching satisfies mutual correlated agreement up to capacity. |

The research-direction statements are prime-field open conjectures, not proved literature theorems. Their extension-field variants are not yet formalized.
