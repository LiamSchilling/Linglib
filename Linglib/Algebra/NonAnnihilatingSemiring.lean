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

/-- Attaches `⊥` to a type as an annihilator -/
def WithAnnihilator (R : Type*) := WithBot R

/-- The canonical map from `R` into `WithAnnihilator R` -/
@[coe, match_pattern] def nonz : R → WithAnnihilator R := WithBot.some

namespace WithAnnihilator

lemma some_eq_nonz (a : R) : some a = nonz a := rfl

@[simp] lemma coe_eq_nonz (a : R) : (a : WithBot R) = nonz a := rfl

@[simp] lemma nonz_eq_nonz (a b : R) : nonz a = nonz b ↔ a = b := Option.some_inj

instance coe : Coe R (WithAnnihilator R) := ⟨nonz⟩

instance bot : Bot (WithAnnihilator R) := WithBot.bot

instance zero : Zero (WithAnnihilator R) where
  zero := ⊥

instance one [One R] : One (WithAnnihilator R) where
  one := nonz 1

instance add [Add R] : Add (WithAnnihilator R) where
  add A B := Option.casesOn' A B (fun a => nonz (Option.casesOn' B a (a + .)))

instance mul [Mul R] : Mul (WithAnnihilator R) where
  mul A B := Option.casesOn' A 0 (fun a => Option.map (a * .) B)

lemma none_eq_zero : none = (0 : WithAnnihilator R) := rfl

lemma some_eq_one [One R] : some 1 = (1 : WithAnnihilator R) := rfl

@[simp] lemma add_nonz [Add R] (a b : R) : nonz a + nonz b = nonz (a + b) := rfl

@[simp] lemma mul_nonz [Mul R] (a b : R) : nonz a * nonz b = nonz (a * b) := rfl

instance addZeroClass [Add R] : AddZeroClass (WithAnnihilator R) where
  zero_add := by intro A; rfl
  add_zero := by intro A; cases A <;> rfl

instance addSemigroup [AddSemigroup R] : AddSemigroup (WithAnnihilator R) where
  add_assoc := by
    intro A B C
    cases A; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    cases B; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    cases C; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    simp; apply add_assoc

instance addCommMagma [AddCommMagma R] : AddCommMagma (WithAnnihilator R) where
  add_comm := by
    intro A B
    cases A; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    cases B; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    simp; apply add_comm

instance mulZeroClass [Mul R] : MulZeroClass (WithAnnihilator R) where
  zero_mul := by intro A; rfl
  mul_zero := by intro A; cases A <;> rfl

instance mulOneClass [MulOneClass R] : MulOneClass (WithAnnihilator R) where
  one_mul := by intro A; rw[←some_eq_one, some_eq_nonz]; cases A; rfl; rw[some_eq_nonz]; simp
  mul_one := by intro A; rw[←some_eq_one, some_eq_nonz]; cases A; rfl; rw[some_eq_nonz]; simp

instance semigroup [Semigroup R] : Semigroup (WithAnnihilator R) where
  mul_assoc := by
    intro A B C
    cases A; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    cases B; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    cases C; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    simp; apply mul_assoc

instance commMagma [CommMagma R] : CommMagma (WithAnnihilator R) where
  mul_comm := by
    intro A B
    cases A; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    cases B; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    simp; apply mul_comm

instance addMonoid [AddSemigroup R] : AddMonoid (WithAnnihilator R) :=
  { addSemigroup, addZeroClass with
  nsmul n A := match n with | 0 => 0 | n' + 1 => Option.map (fun a => Nat.repeat (. + a) n' a) A
  nsmul_succ := by intro n A; cases n <;> cases A <;> rfl }

instance addCommSemigroup [AddCommSemigroup R] : AddCommSemigroup (WithAnnihilator R) :=
  { addSemigroup, addCommMagma with }

instance monoid [Monoid R] : Monoid (WithAnnihilator R) :=
  { semigroup, mulOneClass with
  npow n A := match n with | 0 => 1 | n' + 1 => Option.map (fun a => Nat.repeat (. * a) n' a) A
  npow_succ := by intro n A; cases n <;> (cases A; rfl; simp; rfl) }

instance commSemigroup [CommSemigroup R] : CommSemigroup (WithAnnihilator R) :=
  { semigroup, commMagma with }

instance addCommMonoid [AddCommSemigroup R] : AddCommMonoid (WithAnnihilator R) :=
  { addMonoid, addCommSemigroup with }

instance commMonoid [CommMonoid R] : CommMonoid (WithAnnihilator R) :=
  { monoid, commSemigroup with }

instance distrib [Distrib R] : Distrib (WithAnnihilator R) where
  left_distrib := by
    intro A B C
    cases A; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    cases B; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    cases C; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    simp; apply left_distrib
  right_distrib := by
    intro A B C
    cases A; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    cases B; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    cases C; rw[none_eq_zero]; simp; rw[some_eq_nonz]
    simp; apply right_distrib

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
  { semiring, WithBot.semilatticeSup, WithBot.orderBot with
  add_eq_sup := by
    intro A B
    cases A; rw[none_eq_zero]; simp; apply WithBot.orderBot.bot_le
    nth_rw 1 [some_eq_nonz]; rw[WithBot.some_eq_coe]
    cases B; rw[none_eq_zero]; simp; apply WithBot.orderBot.bot_le
    nth_rw 1 [some_eq_nonz]; rw[WithBot.some_eq_coe]
    rw[←WithBot.coe_sup]; simp; apply self.add_eq_sup }

/-- An commutative and idempotent semiring for `WithAnnihilator R`
given a non-annihilating commutative and idempotent semiring for `R`-/
instance idemCommSemiring [NonAnnihilatingIdemCommSemiring R] :
    IdemCommSemiring (WithAnnihilator R) :=
  { commSemiring, idemSemiring with }

end WithAnnihilator
