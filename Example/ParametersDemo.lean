import RsProximity.Parameters

/-!
# Demo: the FRI parameter calculator

Plug in a degree bound k, a domain size n, and a security target in
bits; `mkReport` computes the rate, the three radii (unique decoding,
Johnson lower bound, capacity) and the minimal query count per regime,
all by exact rational arithmetic. This file reproduces the discussion
table from the README/session notes and demonstrates production-scale
inputs (k = 2^17, blowups 2, 4, 8).

The Johnson row is certified: `johnsonCertified = true` means the δ
used there provably sits below the Johnson radius
(`johnsonLower_le_johnsonRadius`), so that row's query count is
justified by the proved literature regime (BCIKS/Guruswami–Sudan), not
by a conjecture.
-/

open RsProximity

-- ---------------------------------------------------------------------
-- Toy sizes (the README table): blowup 2, 4, 8 at 100-bit security.
-- The Johnson lower bound is coarse at toy sizes (padding of 1/n), so
-- that row is conservative there; see the production sizes below.
-- ---------------------------------------------------------------------

-- rate 1/2, UD 1/4, Johnson LB 0 (padding too coarse at n = 2, hence
-- none), capacity 1/2; queries: UD 241, capacity 100
#eval mkReport 1 2 100 100000

-- rate 1/4, UD 3/8, Johnson 1/2 (exact: 1·4 is a square), capacity 3/4;
-- queries: UD 148, Johnson 100, capacity 50
#eval mkReport 1 4 100 100000

-- rate 1/8, UD 7/16, Johnson LB 5/8 (true 1 − 1/√8 ≈ 0.646), capacity
-- 7/8; queries: UD 121, Johnson 71, capacity 34
#eval mkReport 1 8 100 100000

-- ---------------------------------------------------------------------
-- Production-scale: k = 2^17, blowups 2, 4, 8 (n = 2^18, 2^19, 2^20).
-- ---------------------------------------------------------------------

-- rate 1/2, Johnson LB = 19195/65536 ≈ 0.29289 (true 1 − 1/√2 ≈
-- 0.29290); queries: UD 241, Johnson 201, capacity 100
#eval mkReport (2^17) (2^18) 100 100000

-- rate 1/4, Johnson LB = 1/2 (exact, k·n = 2^36 is a square); queries:
-- UD 148, Johnson 100, capacity 50
#eval mkReport (2^17) (2^19) 100 100000

-- rate 1/8, Johnson LB = 84731/131072 ≈ 0.64644; queries: UD 121,
-- Johnson 67, capacity 34
#eval mkReport (2^17) (2^20) 100 100000

-- ---------------------------------------------------------------------
-- Spot checks with exact values (regression tests).
-- ---------------------------------------------------------------------

-- δ = 1/2 at 100 bits: (1/2)^100 = 2^(-100) exactly, so t = 100.
example : leastQueries (1/2 : ℚ) 100 10000 = some 100 := by native_decide

-- k·n a perfect square: the Johnson lower bound is exact.
example : johnsonLower 1 4 = 1/2 := by native_decide
example : johnsonLower (2^17) (2^19) = 1/2 := by native_decide

-- The Johnson row is always certified (n > 0).
example : (mkReport (2^17) (2^18) 100 100000).johnsonCertified = true := by native_decide
