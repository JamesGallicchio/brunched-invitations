import Mathlib

namespace BunchedImplications

/-! ## Propositions -/

/-- Propositions, with atoms in sort `P` -/
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

namespace Typ
scoped notation a " -* " b => dandy a b
scoped notation a " * " b => star a b
end Typ

open Typ


/-- Bunches, the contexts of bunched logic. -/
inductive Bunch (P : Sort u)
| prop : Typ P → Bunch P
| cunit : Bunch P
| comma : Bunch P → Bunch P → Bunch P
| sunit : Bunch P
| semi : Bunch P → Bunch P → Bunch P

namespace Bunch
scoped infixr:10 " , " => Bunch.comma
scoped infixr:10 " ; " => Bunch.semi
end Bunch

open Bunch in
/-- `BunchSubtree B b` iff `b` is a subtree of `B` -/
inductive BunchSubtree {P : Sort u} : Bunch P → Bunch P → Prop
| refl : BunchSubtree b b
| commaL : BunchSubtree BL b → BunchSubtree (BL, BR) b
| commaR : BunchSubtree BR b → BunchSubtree (BL, BR) b
| semiL : BunchSubtree BL b → BunchSubtree (BL; BR) b
| semiR : BunchSubtree BR b → BunchSubtree (BL; BR) b

namespace BunchSubtree

attribute [refl] refl
attribute [simp] refl commaL commaR semiL semiR

open Bunch in
theorem comma_inv :
  BunchSubtree (BL, BR) b ↔
    BunchSubtree BL b ∨ BunchSubtree BR b ∨ b = (BL, BR) := by
  constructor
  · intro h; cases h <;> simp_all
  · intro h; cases h <;> aesop

open Bunch in
theorem semi_inv :
  BunchSubtree (BL; BR) b ↔
    BunchSubtree BL b ∨ BunchSubtree BR b ∨ b = (BL; BR) := by
  constructor
  · intro h; cases h <;> simp_all
  · intro h; cases h <;> aesop

theorem trans : BunchSubtree b1 b2 → BunchSubtree b2 b3 → BunchSubtree b1 b3 := by
  intro h1 h2
  induction h1 <;> cases h2 <;> simp_all

end BunchSubtree

open Bunch in
/-- `BunchSubtreeSubst B1 b1 B2 b2` iff `B1` and `B2` are identical
except for one subtree at which `b2` was substituted for `b1`.

```
    B1       B2
   /| \     /| \
  a b b1   a b b2
```
-/
inductive BunchSubtreeSubst {P : Sort u}
  : Bunch P → Bunch P → Bunch P → Bunch P → Prop
| refl : BunchSubtreeSubst b1 b1 b2 b2
| commaR
  : BunchSubtreeSubst B1 b1 B2 b2 →
    BunchSubtreeSubst (B, B1) b1 (B, B2) b2
| commaL
  : BunchSubtreeSubst B1 b1 B2 b2 →
    BunchSubtreeSubst (B1, B) b1 (B2, B) b2
| semiR
  : BunchSubtreeSubst B1 b1 B2 b2 →
    BunchSubtreeSubst (B; B1) b1 (B; B2) b2
| semiL
  : BunchSubtreeSubst B1 b1 B2 b2 →
    BunchSubtreeSubst (B1; B) b1 (B2; B) b2

namespace BunchSubtreeSubst

attribute [refl] refl
attribute [simp] refl commaR commaL semiR semiL

theorem iff_subtree : BunchSubtreeSubst B1 b1 B1 b1 ↔ BunchSubtree B1 b1 := by
  constructor
  · intro h
    have : _ → _ → _ := by
      apply h.rec (motive := fun B1 b1 B2 b2 _ => B1 = B2 → b1 = b2 → BunchSubtree B1 b1)
        <;> simp_all
    simp_all
  · intro h
    induction h <;> simp_all

@[simp] theorem subtreeL : BunchSubtreeSubst B1 b1 B2 b2 → BunchSubtree B1 b1 := by
  intro h; induction h <;> simp_all

@[simp] theorem subtreeR : BunchSubtreeSubst B1 b1 B2 b2 → BunchSubtree B2 b2 := by
  intro h; induction h <;> simp_all

theorem symm : BunchSubtreeSubst B1 b1 B2 b2 → BunchSubtreeSubst B2 b2 B1 b1 := by
  intro h
  induction h <;> simp_all

end BunchSubtreeSubst

/-- Bunch with a hole, written as `Γ(-)` in the original paper.

Probably better to always reason about `BunchSubtreeSubst`s directly. -/
structure BunchWithHole (P) where
  toFun : Bunch P → Bunch P
  subtreeSubst : ∀ b1 b2, BunchSubtreeSubst (toFun b1) b1 (toFun b2) b2

namespace BunchWithHole

instance : CoeFun (BunchWithHole P) (λ _ => Bunch P → Bunch P) :=
  ⟨BunchWithHole.toFun⟩

end BunchWithHole

open Bunch in
/-- This is the relation on bunches
which we close over to get bunch equivalence. -/
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
| subtree (h : BunchSubtreeSubst B1 b1 B2 b2) : BunchPreEquiv b1 b2 → BunchPreEquiv B1 B2

/-- Equivalence on bunches. -/
def BunchEquiv {P : Type u} : Bunch P → Bunch P → Prop :=
  EqvGen BunchPreEquiv

def BunchEquiv.is_equivalence : Equivalence (@BunchEquiv P) :=
  EqvGen.is_equivalence _

instance : HasEquiv (Bunch P) := ⟨BunchEquiv⟩



open Bunch in
inductive Entails {P : Type u} : Bunch P → Typ P → Prop
| id : Entails (prop φ) φ
| equiv :
  BunchEquiv Γ Δ →
  Entails Γ φ →
  Entails Δ φ
| weaken :
  BunchSubtreeSubst Γ (semi Δ Δ') Γ' (Δ) →
  Entails Γ' φ →
  Entails Γ φ
| contract :
  BunchSubtreeSubst Γ (Δ) Γ' (semi Δ Δ) →
  Entails Γ' φ →
  Entails Γ φ
/- TODO write down rest of the rules -/
| empI : Entails cunit emp
| empE :
  BunchSubtreeSubst Γ cunit Γ' Δ →
  Entails Γ χ →
  Entails Δ emp →
  Entails Γ' χ
| dandyI :
  Entails (comma Γ (prop φ)) ψ →
  Entails Γ (φ -* ψ)
| dandyE :
  Entails Γ (φ -* ψ) →
  Entails Δ φ        →
    Entails (Γ, Δ) ψ
| starI :
  Entails Γ φ →
  Entails Δ ψ →
  Entails (comma Γ Δ) (star φ ψ)
| starE :
  BunchSubtreeSubst Γ (comma (prop φ) (prop ψ)) Γ' Δ  →
  Entails Γ χ →
  Entails Δ (star φ ψ) →
  Entails Γ' χ
| trI :
  BunchSubtreeSubst Γ sunit Γ' Δ →
  Entails Γ χ →
  Entails Δ tr →
  Entails Γ' χ
| trE : Entails sunit tr
| arrI :
  Entails (semi Γ (prop φ)) ψ →
  Entails Γ (arr φ ψ)
| arrE :
  Entails Γ (arr φ ψ) →
  Entails Δ φ         →
  Entails (Γ; Δ) ψ
| andI :
  Entails Γ φ →
  Entails Δ ψ →
  Entails (semi Γ Δ) (and φ ψ)
| andE :
  BunchSubtreeSubst Γ (semi (prop φ) (prop ψ)) Γ' Δ  →
  Entails Γ χ →
  Entails Δ (and φ ψ) →
  Entails Γ' χ
| orI1 :
  Entails Γ φ₁ →
  Entails Γ (or φ₁ φ₂)
| orI2 :
  Entails Γ φ₂ →
  Entails Γ (or φ₁ φ₂)
| orE :
  BunchSubtreeSubst Δ (prop φ) Δ' (prop ψ) →
  BunchSubtreeSubst Δ (prop φ) Δ'' Γ →
  Entails Γ (or φ ψ) →
  Entails Δ χ  →
  Entails Δ' χ →
  Entails Δ'' χ
| flsE :
  Entails Γ fls →
  Entails Γ φ

theorem id_admissible
  : Entails (.prop φ) φ
  := by
  sorry

theorem cut_admissible {Γφ ΓΔ Δ : Bunch P} {φ : Typ P}
    (hΓ : BunchSubtreeSubst ΓΔ Δ Γφ (.prop φ))
  : Entails Γφ ψ → Entails Δ φ →
    Entails ΓΔ ψ
  := by
  sorry
