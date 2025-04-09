import Linglib.Algebra.NonAnnihilatingSemiring

/-!
### Max-Tropical Semirings

Tropicalization of semirings making supremum `+` and sum `*`.
Mathlib's `Tropical` induces a min-tropical semiring (making infimum `+`),
which is not compatible with any kind of `IdemSemiring` (supremum is `+`).
The max-tropicalization produces a `NonAnnihilatingIdemSemiring`.

## Main declarations

* `Antitropical`: induces a max-tropical semiring on a type
* `Antitropical.nonAnnihilatingIdemSemiring`: a
  non-annihilating idempotent semiring for `Antitropical R`
  given a supremum semilattice and add monoid for `R`

 -/

/-- induces a max-tropical semiring on a type -/
def Antitropical (R : Type*) := R

namespace Antitropical

/-- The canonical map from `R` into `Antitropical R` -/
def trop : R → Antitropical R :=
  id

/-- The canonical map from `Antitropical R` into `R` -/
def untrop : Antitropical R → R :=
  id

theorem eq_trop (a : R) : a = trop a := rfl

theorem eq_untrop (a : Antitropical R) : a = untrop a := rfl

theorem trop_inj (a b : R) : trop a = trop b ↔ a = b := Iff.rfl

theorem untrop_inj (a b : Antitropical R) : untrop a = untrop b ↔ a = b := Iff.rfl

@[simp] theorem untrop_trop (a : R) : untrop (trop a) = a := rfl

@[simp] theorem trop_untrop (a : Antitropical R) : trop (untrop a) = a := rfl

instance le [self : LE R] : LE (Antitropical R) :=
  self

instance lt [self : LT R] : LT (Antitropical R) :=
  self

instance orderBot [LE R] [self : OrderBot R] : OrderBot (Antitropical R) :=
  self

instance orderTop [LE R] [self : OrderTop R] : OrderTop (Antitropical R) :=
  self

instance preorder [self : Preorder R] : Preorder (Antitropical R) :=
  self

instance partialOrder [self : PartialOrder R] : PartialOrder (Antitropical R) :=
  self

instance linearOrder [self : LinearOrder R] : LinearOrder (Antitropical R) :=
  self

instance semilatticeInf [self : SemilatticeInf R] : SemilatticeInf (Antitropical R) :=
  self

instance semilatticeSup [self : SemilatticeSup R] : SemilatticeSup (Antitropical R) :=
  self

instance lattice [self : Lattice R] : Lattice (Antitropical R) :=
  self

instance zero [Bot R] : Zero (Antitropical R) where
  zero := trop ⊥

instance one [Zero R] : One (Antitropical R) where
  one := trop 0

instance add [Max R] : Add (Antitropical R) where
  add a b := trop (a ⊔ b)

instance mul [Add R] : Mul (Antitropical R) where
  mul a b := untrop a + untrop b

theorem bot_eq_zero [Bot R] : (⊥ : R) = (0 : Antitropical R) := rfl

theorem zero_eq_one [Zero R] : (0 : R) = (1 : Antitropical R) := rfl

theorem trop_add [Max R] (a b : R) : a ⊔ b = trop a + trop b := rfl

theorem untrop_add [Max R] (a b : Antitropical R) : untrop a ⊔ untrop b = a + b := rfl

theorem trop_mul [Add R] (a b : R) : a + b = trop a * trop b := rfl

theorem untrop_mul [Add R] (a b : Antitropical R) : untrop a + untrop b = a * b := rfl

theorem trop_inf [SemilatticeInf R] (a b : R) : a ⊓ b = trop a ⊓ trop b := rfl

theorem untrop_inf [SemilatticeInf R] (a b : Antitropical R) : untrop a ⊓ untrop b = a ⊓ b := rfl

theorem trop_sup [SemilatticeSup R] (a b : R) : a ⊔ b = trop a ⊔ trop b := rfl

theorem untrop_sup [SemilatticeSup R] (a b : Antitropical R) : untrop a ⊔ untrop b = a ⊔ b := rfl

instance addZeroClass {R} [SemilatticeSup R] [OrderBot R] : AddZeroClass (Antitropical R) where
  zero_add := sorry
  add_zero := sorry

instance addSemigroup [SemilatticeSup R] : AddSemigroup (Antitropical R) where
  add_assoc := sorry

instance addCommMagma [SemilatticeSup R] : AddCommMagma (Antitropical R) where
  add_comm := sorry

instance addMonoid [SemilatticeSup R] [OrderBot R] : AddMonoid (Antitropical R) :=
  { addSemigroup, addZeroClass with
  nsmul := nsmulRecAuto }

instance mulZeroClass [SemilatticeSup R] [OrderBot R] [Add R] : MulZeroClass (Antitropical R) where
  zero_mul := sorry
  mul_zero := sorry

instance mulOneClass [AddZeroClass R] : MulOneClass (Antitropical R) where
  one_mul := sorry
  mul_one := sorry

instance semigroup [AddSemigroup R] : Semigroup (Antitropical R) where
  mul_assoc := sorry

instance commMagma [AddCommMagma R] : CommMagma (Antitropical R) where
  mul_comm := sorry

instance monoid [AddMonoid R] : Monoid (Antitropical R) :=
  { semigroup, mulOneClass with
  npow := npowRecAuto }

instance distrib [SemilatticeSup R] [Add R] [AddLeftMono R] [AddRightMono R] : Distrib (Antitropical R) where
  left_distrib := sorry
  right_distrib := sorry

/-- A non-annihilating idempotent semiring for `Antitropical R`
given a supremum semilattice and an ordered add monoid for `R` -/
instance nonAnnihilatingIdemSemiring [SemilatticeSup R] [AddMonoid R] [AddLeftMono R] [AddRightMono R] :
    NonAnnihilatingIdemSemiring (Antitropical R) :=
  { addSemigroup, addCommMagma, distrib, monoid, semilatticeSup with }

/-- A non-annihilating idempotent and commutative semiring for `Antitropical R`
given a supremum semilattice and an ordered and commutative add monoid for `R` -/
instance nonAnnihilatingIdemCommSemiring [SemilatticeSup R] [OrderedAddCommMonoid R] :
    NonAnnihilatingIdemCommSemiring (Antitropical R) := sorry
--  { nonAnnihilatingIdemSemiring, commMagma with }

/-- An idempotent semiring for `Antitropical R`
given a supremum semilattice with a minimum and an ordered add monoid for `R` -/
instance idemSemiring [SemilatticeSup R] [OrderBot R] [AddMonoid R] [AddLeftMono R] [AddRightMono R] :
    IdemSemiring (Antitropical R) :=
  { addMonoid, addCommMagma, distrib, mulZeroClass, monoid, semilatticeSup, orderBot with }

/-- An idempotent and commutative semiring for `Antitropical R`
given a supremum semilattice with a minimum and an ordered and commutative add monoid for `R` -/
instance idemCommSemiring [SemilatticeSup R] [OrderBot R] [OrderedAddCommMonoid R] :
    IdemCommSemiring (Antitropical R) := sorry
--  { idemSemiring, commMagma with }

end Antitropical
