import Mathlib.Algebra.Order.Kleene
import Mathlib.Order.WithBot
import Mathlib.Tactic.NthRewrite

/-!
# Non-Annihilating Semirings

Semirings without a necessary `0` member (annihilator).
`WithAnnihilator` attaches the `⊥` annihilator
while preserving commutativity and idempotence.

## Main declarations

* `NonAnnihilatingSemiring`: a not-necessarily-annihilating semiring
* `WithAnnihilator`: attaches `⊥` to a type as an annihilator
* `WithAnnihilator.semiring`: a semiring for `WithAnnihilator R`
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
    NonAnnihilatingNonUnitalSemiring R, NonAnnihilatingNonAssocSemiring R, Monoid R

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

/-- Attaches `⊥` to a type as an annihilator -/
def WithAnnihilator (R : Type*) := WithBot R

/-- The canonical map from `R` into `WithAnnihilator R` -/
@[match_pattern] def nonz : R → WithAnnihilator R :=
  WithBot.some

namespace WithAnnihilator

instance coe : Coe R (WithAnnihilator R) :=
  ⟨nonz⟩

theorem some_eq_nonz (a : R) : some a = nonz a := rfl

theorem coe_eq_nonz (a : R) : (a : WithBot R) = nonz a := rfl

theorem nonz_inj (a b : R) : nonz a = nonz b ↔ a = b := Option.some_inj

instance le [LE R] : LE (WithAnnihilator R) :=
  WithBot.le

instance lt [LT R] : LT (WithAnnihilator R) :=
  WithBot.lt

instance bot : Bot (WithAnnihilator R) :=
  WithBot.bot

instance orderBot [LE R] : OrderBot (WithAnnihilator R) :=
  WithBot.orderBot

instance orderTop [LE R] [OrderTop R] : OrderTop (WithAnnihilator R) :=
  WithBot.orderTop

instance preorder [Preorder R] : Preorder (WithAnnihilator R) :=
  WithBot.preorder

instance partialOrder [PartialOrder R] : PartialOrder (WithAnnihilator R) :=
  WithBot.partialOrder

instance linearOrder [LinearOrder R] : LinearOrder (WithAnnihilator R) :=
  WithBot.linearOrder

instance semilatticeInf [SemilatticeInf R] : SemilatticeInf (WithAnnihilator R) :=
  WithBot.semilatticeInf

instance semilatticeSup [SemilatticeSup R] : SemilatticeSup (WithAnnihilator R) :=
  WithBot.semilatticeSup

instance lattice [Lattice R] : Lattice (WithAnnihilator R) :=
  WithBot.lattice

instance zero : Zero (WithAnnihilator R) where
  zero := ⊥

instance one [One R] : One (WithAnnihilator R) where
  one := nonz 1

instance add [Add R] : Add (WithAnnihilator R) where
  add A B := Option.casesOn' A B (fun a => nonz (Option.casesOn' B a (a + .)))

instance mul [Mul R] : Mul (WithAnnihilator R) where
  mul A B := Option.casesOn' A 0 (fun a => Option.map (a * .) B)

/-- Recursor for `WithAnnihilator` using the preferred forms `0` and `nonz a` -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recZeroNonz {C : WithAnnihilator R → Sort*} (z : C 0) (n : ∀ a, C (nonz a)) : ∀ A, C A
| 0 => z
| (a : R) => n a

@[simp] theorem zero_le [LE R] (A : WithAnnihilator R) : 0 ≤ A := orderBot.bot_le A

theorem none_eq_zero : none = (0 : WithAnnihilator R) := rfl

theorem bot_eq_zero : ⊥ = (0 : WithAnnihilator R) := rfl

theorem nonz_eq_one [One R] : nonz 1 = (1 : WithAnnihilator R) := rfl

theorem nonz_add [Add R] (a b : R) : nonz (a + b) = nonz a + nonz b := rfl

theorem nonz_mul [Mul R] (a b : R) : nonz (a * b) = nonz a * nonz b := rfl

theorem nonz_inf [SemilatticeInf R] (a b : R) : nonz (a ⊓ b) = nonz a ⊓ nonz b := rfl

theorem nonz_sup [SemilatticeSup R] (a b : R) : nonz (a ⊔ b) = nonz a ⊔ nonz b := rfl

instance addZeroClass [Add R] : AddZeroClass (WithAnnihilator R) where
  zero_add := by intro A; rfl
  add_zero := by intro A; cases A <;> rfl

instance addSemigroup [AddSemigroup R] : AddSemigroup (WithAnnihilator R) where
  add_assoc := by
    intro A B C
    cases A <;> cases B <;> cases C <;> simp[←nonz_add, nonz_inj, add_assoc]

instance addCommMagma [AddCommMagma R] : AddCommMagma (WithAnnihilator R) where
  add_comm := by
    intro A B
    cases A <;> cases B <;> simp[←nonz_add, nonz_inj, add_comm]

instance mulZeroClass [Mul R] : MulZeroClass (WithAnnihilator R) where
  zero_mul := by intro A; rfl
  mul_zero := by intro A; cases A <;> rfl

instance mulOneClass [MulOneClass R] : MulOneClass (WithAnnihilator R) where
  one_mul := by intro A; cases A <;> simp[←nonz_eq_one, ←nonz_mul]
  mul_one := by intro A; cases A <;> simp[←nonz_eq_one, ←nonz_mul]

instance semigroup [Semigroup R] : Semigroup (WithAnnihilator R) where
  mul_assoc := by
    intro A B C
    cases A <;> cases B <;> cases C <;> simp[←nonz_mul, nonz_inj, mul_assoc]

instance commMagma [CommMagma R] : CommMagma (WithAnnihilator R) where
  mul_comm := by
    intro A B
    cases A <;> cases B <;> simp[←nonz_mul, nonz_inj, mul_comm]

instance addMonoid [AddSemigroup R] : AddMonoid (WithAnnihilator R) :=
  { addSemigroup, addZeroClass with
  nsmul n A := match n with | 0 => 0 | n' + 1 => Option.map (fun a => Nat.repeat (. + a) n' a) A
  nsmul_succ := by
    intro n A
    cases n <;> cases A <;> rfl }

instance addCommSemigroup [AddCommSemigroup R] : AddCommSemigroup (WithAnnihilator R) :=
  { addSemigroup, addCommMagma with }

instance monoid [Monoid R] : Monoid (WithAnnihilator R) :=
  { semigroup, mulOneClass with
  npow n A := match n with | 0 => 1 | _ + 1 => Option.map (. ^ n) A
  npow_succ := by
    intro n A
    cases n <;> cases A
    <;> simp[Option.map, none_eq_zero, some_eq_nonz, ←nonz_mul, nonz_inj, pow_succ] }

instance commSemigroup [CommSemigroup R] : CommSemigroup (WithAnnihilator R) :=
  { semigroup, commMagma with }

instance addCommMonoid [AddCommSemigroup R] : AddCommMonoid (WithAnnihilator R) :=
  { addMonoid, addCommSemigroup with }

instance commMonoid [CommMonoid R] : CommMonoid (WithAnnihilator R) :=
  { monoid, commSemigroup with }

instance distrib [Distrib R] : Distrib (WithAnnihilator R) where
  left_distrib := by
    intro A B C
    cases A <;> cases B <;> cases C <;> simp[←nonz_add, ←nonz_mul, nonz_inj, left_distrib]
  right_distrib := by
    intro A B C
    cases A <;> cases B <;> cases C <;> simp[←nonz_add, ←nonz_mul, nonz_inj, right_distrib]

/-- A non-unital, non-associative semiring for `WithAnnihilator R`
given a non-annihilating, non-unital, non-associative semiring for `R`-/
instance nonUnitalNonAssocSemiring [NonAnnihilatingNonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (WithAnnihilator R) :=
  { addCommMonoid, distrib, mulZeroClass with }

/-- A non-unital semiring for `WithAnnihilator R`
given a non-annihilating, non-unital semiring for `R`-/
instance nonUnitalSemiring [NonAnnihilatingNonUnitalSemiring R] :
    NonUnitalSemiring (WithAnnihilator R) :=
  { nonUnitalNonAssocSemiring, semigroup with }

/-- A non-associative semiring for `WithAnnihilator R`
given a non-annihilating, non-associative semiring for `R`-/
instance nonAssocSemiring [NonAnnihilatingNonAssocSemiring R] :
    NonAssocSemiring (WithAnnihilator R) :=
  { nonUnitalNonAssocSemiring, mulOneClass with }

/-- A semiring for `WithAnnihilator R`
given a non-annihilating semiring for `R`-/
instance semiring [NonAnnihilatingSemiring R] :
    Semiring (WithAnnihilator R) :=
  { nonUnitalSemiring, nonAssocSemiring with }

/-- A commutative semiring for `WithAnnihilator R`
given a non-annihilating commutative semiring for `R`-/
instance commSemiring [NonAnnihilatingCommSemiring R] :
    CommSemiring (WithAnnihilator R) :=
  { semiring, commMonoid with }

/-- An idempotent semiring for `WithAnnihilator R`
given a non-annihilating idempotent semiring for `R`-/
instance idemSemiring [self : NonAnnihilatingIdemSemiring R] :
    IdemSemiring (WithAnnihilator R) :=
  { semiring, semilatticeSup, orderBot with
  add_eq_sup := by
    intro A B
    cases A <;> cases B <;> simp[←nonz_add, ←nonz_sup, nonz_inj, self.add_eq_sup] }

/-- An commutative and idempotent semiring for `WithAnnihilator R`
given a non-annihilating commutative and idempotent semiring for `R`-/
instance idemCommSemiring [NonAnnihilatingIdemCommSemiring R] :
    IdemCommSemiring (WithAnnihilator R) :=
  { commSemiring, idemSemiring with }

end WithAnnihilator
