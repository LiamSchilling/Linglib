import Mathlib.Algebra.Order.Kleene
import Mathlib.Order.WithBot

/-!
# Non-Annihilating Semirings

Semirings without a necessary `0` member.
Instances show that `WithBot` introduces an annihilator `⊥`
which is also closed under commutativity and idempotence.

## Main declarations

* `NonAnnihilatingSemiring`: a not-necessarily-annihilating semiring
* `annihilator_semiring`: a semiring for `WithBot R`
  given a non-annihilating semiring for `R`

 -/

/-- A not-necessarily-annihilating, not-necessarily-unital, not-necessarily-associative
semiring -/
class NonAnnihilatingNonUnitalNonAssocSemiring (R : Type*) extends
    AddCommSemigroup R, Distrib R

/-- A not-necessarily-annihilating, not-necessarily-unital
semiring -/
class NonAnnihilatingNonUnitalSemiring (R : Type*) extends
    NonAnnihilatingNonUnitalNonAssocSemiring R, Semigroup R

/-- A not-necessarily-annihilating, not-necessarily-associative
semiring -/
class NonAnnihilatingNonAssocSemiring (R : Type*) extends
    NonAnnihilatingNonUnitalNonAssocSemiring R, MulOneClass R

/-- A not-necessarily-annihilating
semiring -/
class NonAnnihilatingSemiring (R : Type*) extends
    NonAnnihilatingNonUnitalSemiring R, NonAnnihilatingNonAssocSemiring R

/-- A not-necessarily-annihilating
semiring with commutative multiplication -/
class NonAnnihilatingCommSemiring (R : Type*) extends
    NonAnnihilatingSemiring R, CommMonoid R

/-- A not-necessarily-annihilating
semiring with idempotent addition -/
class NonAnnihilatingIdemSemiring (R : Type*) extends
    NonAnnihilatingSemiring R, SemilatticeSup R where
  protected sup := (. + .)
  protected add_eq_sup : ∀ a b : R, a + b = a ⊔ b := by intros; rfl

/-- A not-necessarily-annihilating
semiring with commutative multiplication and idempotent addition -/
class NonAnnihilatingIdemCommSemiring (R : Type*) extends
    NonAnnihilatingCommSemiring R, NonAnnihilatingIdemSemiring R

namespace Semiring

instance annihilator_zero : Zero (WithBot R) where
  zero := none

instance annihilator_one [One R] : One (WithBot R) where
  one := some 1

instance annihilator_add [Add R] : Add (WithBot R) where
  add A B := A.casesOn' B (fun a => some (B.casesOn' a (a + .)))

instance annihilator_mul [Mul R] : Mul (WithBot R) where
  mul A B := A.casesOn' none (fun a => B.map (a * .))

instance annihilator_addSemigroup [AddSemigroup R] : AddSemigroup (WithBot R) where
  add_assoc := sorry

instance annihilator_addCommMagma [AddCommMagma R] : AddCommMagma (WithBot R) where
  add_comm := sorry

instance annihilator_addZeroClass [Add R] : AddZeroClass (WithBot R) where
  zero_add := sorry
  add_zero := sorry

instance annihilator_semigroup [Semigroup R] : Semigroup (WithBot R) where
  mul_assoc := sorry

instance annihilator_commMagma [CommMagma R] : CommMagma (WithBot R) where
  mul_comm := sorry

instance annihilator_mulZeroClass [Mul R] : MulZeroClass (WithBot R) where
  zero_mul := sorry
  mul_zero := sorry

instance annihilator_mulOneClass [One R] [Mul R] : MulOneClass (WithBot R) where
  one_mul := sorry
  mul_one := sorry

instance annihilator_addMonoid [AddSemigroup R] : AddMonoid (WithBot R) :=
  { annihilator_addSemigroup, annihilator_addZeroClass with
  nsmul n A := match n with | 0 => none | n' + 1 => A.map (fun a => n'.repeat (. + a) a)
  nsmul_succ := sorry }

instance annihilator_addCommSemigroup [AddCommSemigroup R] : AddCommSemigroup (WithBot R) :=
  { annihilator_addSemigroup, annihilator_addCommMagma with }

instance annihilator_monoid [Monoid R] : Monoid (WithBot R) :=
  { annihilator_semigroup, annihilator_mulOneClass with
  npow n A := match n with | 0 => 1 | n' + 1 => A.map (fun a => n.repeat (. * a) a)
  npow_succ := sorry }

instance annihilator_commSemigroup [CommSemigroup R] : CommSemigroup (WithBot R) :=
  { annihilator_semigroup, annihilator_commMagma with }

instance annihilator_addCommMonoid [AddCommSemigroup R] : AddCommMonoid (WithBot R) :=
  { annihilator_addMonoid, annihilator_addCommSemigroup with }

instance annihilator_commMonoid [CommMonoid R] : CommMonoid (WithBot R) :=
  { annihilator_monoid, annihilator_commSemigroup with }

instance annihilator_distrib [Distrib R] : Distrib (WithBot R) where
  left_distrib := sorry
  right_distrib := sorry

/-- a non-unital, non-associative semiring for `WithBot R`
given a non-annihilating, non-unital, non-associative semiring for `R`-/
instance annihilator_nonUnitalNonAssocSemiring [NonAnnihilatingNonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (WithBot R) :=
  { annihilator_addCommMonoid, annihilator_distrib, annihilator_mulZeroClass with }

/-- a non-unital semiring for `WithBot R`
given a non-annihilating, non-unital semiring for `R`-/
instance annihilator_nonUnitalSemiring [NonAnnihilatingNonUnitalSemiring R] :
    NonUnitalSemiring (WithBot R) :=
  { annihilator_nonUnitalNonAssocSemiring, annihilator_semigroup with }

/-- a non-associative semiring for `WithBot R`
given a non-annihilating, non-associative semiring for `R`-/
instance annihilator_nonAssocSemiring [NonAnnihilatingNonAssocSemiring R] :
    NonAssocSemiring (WithBot R) :=
  { annihilator_nonUnitalNonAssocSemiring, annihilator_mulOneClass with }

/-- a semiring for `WithBot R`
given a non-annihilating semiring for `R`-/
instance annihilator_semiring [NonAnnihilatingSemiring R] :
    Semiring (WithBot R) :=
  { annihilator_nonUnitalSemiring, annihilator_nonAssocSemiring with }

/-- a commutative semiring for `WithBot R`
given a non-annihilating commutative semiring for `R`-/
instance annihilator_commSemiring [NonAnnihilatingCommSemiring R] :
    CommSemiring (WithBot R) :=
  { annihilator_semiring, annihilator_commMonoid with }

/-- an idempotent semiring for `WithBot R`
given a non-annihilating idempotent semiring for `R`-/
instance annihilator_idemSemiring [NonAnnihilatingIdemSemiring R] :
    IdemSemiring (WithBot R) :=
  { annihilator_semiring, WithBot.semilatticeSup with
  add_eq_sup := sorry
  bot_le := sorry }

/-- an commutative and idempotent semiring for `WithBot R`
given a non-annihilating commutative and idempotent semiring for `R`-/
instance annihilator_idemCommSemiring [NonAnnihilatingIdemCommSemiring R] :
    IdemCommSemiring (WithBot R) :=
  { annihilator_commSemiring, annihilator_idemSemiring with }

end Semiring
