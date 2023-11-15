import Mathlib

namespace BunchedImplications

inductive Typ (P : Sort u)
| atom : P → Typ P
/- Structural connectives -/
| arr : Typ P → Typ P → Typ P
| tr : Typ P
| and : Typ P → Typ P → Typ P
| fls : Typ P
| or : Typ P → Typ P → Typ P
/- Linear connectives -/
| dandy : Typ P → Typ P → Typ P
| emp : Typ P
| star : Typ P → Typ P → Typ P

inductive Bunch (P : Sort u)
| atom : P → Bunch P
| cunit : Bunch P
| comma : Bunch P → Bunch P → Bunch P
| sunit : Bunch P
| semi : Bunch P → Bunch P → Bunch P

scoped infixr:10 " , " => Bunch.comma
scoped infixr:10 " ; " => Bunch.semi

/-- `BunchSubtree B b` if `b` is a subtree of `B` -/
inductive BunchSubtree {P : Sort u} : Bunch P → Bunch P → Prop
| rfl (b : Bunch P) : BunchSubtree b b
| commaL {BL BR b} : BunchSubtree BL b → BunchSubtree (BL, BR) b
| commaR {BL BR b} : BunchSubtree BR b → BunchSubtree (BL, BR) b
| semiL {BL BR b} : BunchSubtree BL b → BunchSubtree (BL; BR) b
| semiR {BL BR b} : BunchSubtree BR b → BunchSubtree (BL; BR) b

namespace BunchSubtree

theorem refl : BunchSubtree b b := .rfl b
theorem trans : BunchSubtree b1 b2 → BunchSubtree b2 b3 → BunchSubtree b1 b3 :=
  sorry

end BunchSubtree

structure BunchWithHole (P) where
  toFun : Bunch P → Bunch P
  subtree : ∀ b, BunchSubtree (toFun b) b

instance : CoeFun (BunchWithHole P) (λ _ => Bunch P → Bunch P) :=
  ⟨BunchWithHole.toFun⟩

inductive BunchPreEquiv {P : Sort u} : Bunch P → Bunch P → Prop
/- Comm. monoid laws for `,` with `cunit` -/
| cunitL : BunchPreEquiv (.cunit, b) b
| cunitR : BunchPreEquiv (b, .cunit) b
| commaAssoc : BunchPreEquiv (b1, b2, b3) ((b1, b2), b3)
| commaComm : BunchPreEquiv (b1, b2) (b2, b1)
/- Comm. monoid laws for `;` with `sunit` -/
| sunitL : BunchPreEquiv (.sunit; b) b
| sunitR : BunchPreEquiv (b; .sunit) b
| semiAssoc : BunchPreEquiv (b1; b2; b3) ((b1; b2); b3)
| semiComm : BunchPreEquiv (b1; b2) (b2; b1)
/- Subtree congruence -/
| subtree (h : BunchWithHole P) : BunchPreEquiv b1 b2 → BunchPreEquiv (h b1) (h b2)

/-- Equivalence on bunches -/
def BunchEquiv {P : Type u} : Bunch P → Bunch P → Prop :=
  EqvGen BunchPreEquiv

def BunchEquiv.is_equivalence : Equivalence (@BunchEquiv P) :=
  EqvGen.is_equivalence _

instance : HasEquiv (Bunch P) := ⟨BunchEquiv⟩

inductive Entails {P : Type u} : Bunch P → Typ P → Prop
/- TODO write down the rules -/
