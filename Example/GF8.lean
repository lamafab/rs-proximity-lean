import Mathlib.Tactic
import Mathlib.Algebra.CharP.Two

-- ============================================================================
-- GF(8), hand-rolled for decidability
-- ============================================================================
--
-- GF(8) = GF(2)[α]/(α³ + α + 1) built as triples of bits with schoolbook
-- multiplication, so that worked examples can evaluate everything with
-- decide. Mathlib's GaloisField and AdjoinRoot do not evaluate with decide
-- (their DecidableEq instances are classical).
--
-- Used by Example/FoldDemo.lean. The Field and CharP instances at the
-- bottom connect G8 to the RsProximity library, whose fold machinery
-- requires [Field F] [CharP F 2].

/-- GF(8) = GF(2)[α]/(α³ + α + 1). Elements are triples (b₀, b₁, b₂),
read as b₀ + b₁α + b₂α². -/
def G8 := Fin 2 × Fin 2 × Fin 2

namespace G8

instance : Zero G8 := ⟨(0, 0, 0)⟩

/-- The multiplicative identity is (1, 0, 0); the product type's own One
instance would be (1, 1, 1), so it is defined explicitly. -/
instance : One G8 := ⟨(1, 0, 0)⟩

/-- Addition is componentwise: XOR on the three 𝔽₂-coordinates. -/
instance : Add G8 := ⟨fun x y => (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)⟩

/-- Multiplication: schoolbook in α, then reduce by α³ = α + 1 (hence
α⁴ = α² + α). cᵢ is the pre-reduction coefficient of αⁱ; α³ folds into
positions 0 and 1, α⁴ into positions 1 and 2. -/
def mul (x y : G8) : G8 :=
  let c₁ := x.1 * y.2.1 + x.2.1 * y.1
  let c₂ := x.1 * y.2.2 + x.2.1 * y.2.1 + x.2.2 * y.1
  let c₃ := x.2.1 * y.2.2 + x.2.2 * y.2.1
  let c₄ := x.2.2 * y.2.2
  (x.1 * y.1 + c₃, c₁ + c₃ + c₄, c₂ + c₄)

instance : Mul G8 := ⟨mul⟩

/-- Multiplicative inverse: x⁶, since x⁷ = 1 for every x ≠ 0 (the unit
group has order 7), and 0⁶ = 0 is the usual junk value. -/
def inv (x : G8) : G8 := x * x * x * x * x * x

instance : Inv G8 := ⟨inv⟩

/-- The primitive element α = (0, 1, 0), a root of X³ + X + 1. Kept as a
def (not an ascribed tuple) so that terms built from it elaborate with
type G8 and pick up the G8 instances above, not the product type's
pointwise ones. -/
def alpha : G8 := (0, 1, 0)

instance : DecidableEq G8 := inferInstanceAs (DecidableEq (Fin 2 × Fin 2 × Fin 2))
instance : Fintype G8 := inferInstanceAs (Fintype (Fin 2 × Fin 2 × Fin 2))

/-- The primitive element. Scoped so importers opt in with `open G8`;
plain notation would forbid α as a binder name downstream. -/
scoped notation "α" => G8.alpha

/-- α² = (0, 0, 1). -/
scoped notation "α²" => α * α

/-- Negation is the identity in characteristic 2. -/
instance : Neg G8 := ⟨id⟩

/-- Subtraction is addition in characteristic 2. -/
instance : Sub G8 := ⟨Add.add⟩

/-- The cast from ℕ: n maps to its parity. -/
def natCastG8 (n : ℕ) : G8 := if n % 2 = 0 then 0 else 1

/-- The cast from ℤ: parity of the absolute value (negation is junk-free
in characteristic 2). -/
def intCastG8 (n : ℤ) : G8 := if n.natAbs % 2 = 0 then 0 else 1

/-- The cast from ℚ: numerator times inverse of denominator, the usual
junk-aware form; only the parity of each matters here. -/
def ratCastG8 (q : ℚ) : G8 := intCastG8 q.num * inv (natCastG8 q.den)

/-- Division: multiply by the inverse. -/
def divG8 (x y : G8) : G8 := x * inv y

instance : Div G8 := ⟨divG8⟩

-- Sanity: the defining relation, the unit-group order used by `inv`,
-- characteristic 2, and the inverse law.
example : α * α * α = α + 1 := by decide
example : ∀ x : G8, x ≠ 0 → x * x * x * x * x * x * x = 1 := by decide
example : ∀ x : G8, x + x = 0 := by decide
example : ∀ x : G8, inv x * x = if x = 0 then 0 else 1 := by decide

-- ----------------------------------------------------------------------------
-- Field and CharP instances, so the RsProximity fold machinery applies
-- ----------------------------------------------------------------------------

/-- GF(8) is a field; every axiom over the 8 elements is decidable. The
cast axioms are parity arithmetic (`omega` on n % 2) plus decidable
equality on G8. -/
instance : Field G8 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  sub_eq_add_neg := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast := natCastG8
  natCast_zero := rfl
  natCast_succ n := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h1 : (n + 1) % 2 = 1 := by omega
      show natCastG8 (n + 1) = natCastG8 n + 1
      unfold natCastG8
      rw [if_neg (by omega : ¬(n + 1) % 2 = 0), if_pos h]
      decide
    · have h1 : (n + 1) % 2 = 0 := by omega
      show natCastG8 (n + 1) = natCastG8 n + 1
      unfold natCastG8
      rw [if_pos h1, if_neg (by omega : ¬n % 2 = 0)]
      decide
  intCast := intCastG8
  intCast_ofNat n := by
    show intCastG8 (n : ℤ) = natCastG8 n
    unfold intCastG8 natCastG8
    rw [Int.natAbs_natCast]
  intCast_negSucc n := by
    show intCastG8 (Int.negSucc n) = -natCastG8 (n + 1)
    unfold intCastG8 natCastG8
    rw [Int.natAbs_negSucc, Nat.succ_eq_add_one]
    rfl
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  inv_zero := by decide
  mul_inv_cancel := by decide
  div_eq_mul_inv := by decide
  ratCast := ratCastG8
  ratCast_def := by
    intro q
    show ratCastG8 q = divG8 (intCastG8 q.num) (natCastG8 q.den)
    rfl
  nnqsmul := fun q x => natCastG8 q.num * inv (natCastG8 q.den) * x
  nnqsmul_def := by intro q x; rfl
  qsmul := fun q x => ratCastG8 q * x
  qsmul_def := by intro q x; rfl
  exists_pair_ne := ⟨0, 1, by decide⟩

/-- GF(8) has characteristic 2: the cast of n vanishes iff n is even. -/
instance : CharP G8 2 where
  cast_eq_zero_iff x := by
    show (natCastG8 x = 0) ↔ 2 ∣ x
    rw [Nat.dvd_iff_mod_eq_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have hc : natCastG8 x = 0 := by unfold natCastG8; rw [if_pos h]
      rw [hc]
      constructor
      · intro _; exact h
      · intro _; rfl
    · have hc : natCastG8 x = 1 := by unfold natCastG8; rw [if_neg (by omega)]
      rw [hc]
      constructor
      · intro h1; exact absurd h1 (by decide)
      · intro h1; omega
end G8

open G8
