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

declare_syntax_cat bi_typ

syntax:50 bi_typ:51 " -* " bi_typ:50 : bi_typ
syntax:50 bi_typ:51 " → "  bi_typ:50 : bi_typ
syntax:60 bi_typ:61 " ∨ "  bi_typ:50 : bi_typ
syntax:70 bi_typ:71 " ∧ "  bi_typ:50 : bi_typ
syntax:70 bi_typ:71 " * "  bi_typ:50 : bi_typ
syntax term:71 : bi_typ

syntax "[bi| " bi_typ " ]" : term
macro_rules
| `([bi| $t:term ]) => `(show Typ _ from $t)
| `([bi| $t1 -* $t2 ]) => `(Typ.dandy [bi| $t1] [bi| $t2])
| `([bi| $t1 → $t2 ]) => `(Typ.arr [bi| $t1] [bi| $t2])
| `([bi| $t1 ∨ $t2 ]) => `(Typ.or [bi| $t1] [bi| $t2])
| `([bi| $t1 ∧ $t2 ]) => `(Typ.and [bi| $t1] [bi| $t2])
| `([bi| $t1 * $t2 ]) => `(Typ.star [bi| $t1] [bi| $t2])

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
scoped infixr:40 " , " => Bunch.comma
scoped infixr:40 " ; " => Bunch.semi
instance : Coe (Typ P) (Bunch P) := ⟨prop⟩
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

theorem symm_iff : BunchSubtreeSubst B1 b1 B2 b2 ↔ BunchSubtreeSubst B2 b2 B1 b1 :=
  ⟨symm, symm⟩

theorem subtree_size_lt {B1 : Bunch P} : BunchSubtree B1 b1 → sizeOf B1 ≥ sizeOf b1 := by
  intro h1
  induction h1 <;> simp <;> linarith

@[simp] theorem left_eq : BunchSubtreeSubst B1 B1 B2 b2 ↔ B2 = b2 := by
  constructor
  · intro h1; cases h1; rfl
    case mp.commaL | mp.semiL =>
      have t := subtree_size_lt <| subtreeL ‹_›
      simp_all
      exfalso
      linarith
    case mp.commaR | mp.semiR =>
      have t := subtree_size_lt <| subtreeL ‹_›
      simp_all
  · intro h1; simp_all

@[simp] theorem right_eq : BunchSubtreeSubst B1 b1 B2 B2 ↔ B1 = b1 :=
  by rw [symm_iff, left_eq]

theorem trans : BunchSubtreeSubst B1 b1 B2 b2 → BunchSubtreeSubst B2 b2 B3 b3
    → BunchSubtreeSubst B1 b1 B3 b3 := by
    intro h1 h2
    induction h1 <;>
    sorry

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

/- This gives access to `≈` notation on bunches. -/
instance : HasEquiv (Bunch P) := ⟨BunchEquiv⟩



set_option hygiene false in
notation:35 Γ:40 " ⊢ " φ:40 => Entails Γ φ

open Bunch in
inductive Entails {P : Type u} : Bunch P → Typ P → Prop
| id {φ : Typ P} :
      φ ⊢ φ
| equiv :
    Γ ≈ Δ →
    Γ ⊢ φ →
      Δ ⊢ φ
| weaken :
    BunchSubtreeSubst Γ (Δ; Δ') Γ' (Δ) →
    Γ' ⊢ φ →
      Γ ⊢ φ
| contract :
    BunchSubtreeSubst Γ Δ Γ' (Δ; Δ) →
    Γ' ⊢ φ →
      Γ ⊢ φ
/- TODO write down rest of the rules -/
| empI : cunit ⊢ emp
| empE :
    BunchSubtreeSubst Γ cunit Γ' Δ →
    Γ ⊢ χ   →
    Δ ⊢ emp →
      Γ' ⊢ χ
| dandyI {φ ψ : Typ P} :
    Γ, φ ⊢ ψ →
      Γ ⊢ [bi| φ -* ψ ]
| dandyE :
    Γ ⊢ [bi| φ -* ψ ] →
    Δ ⊢ φ →
      Γ, Δ ⊢ ψ
| starI :
    Γ ⊢ φ →
    Δ ⊢ ψ →
      Γ, Δ ⊢ [bi| φ * ψ ]
| starE {φ ψ : Typ P} :
    BunchSubtreeSubst Γ (φ, ψ) Γ' Δ  →
    Γ ⊢ χ →
    Δ ⊢ [bi| φ * ψ ] →
      Γ' ⊢ χ
| trI :
    BunchSubtreeSubst Γ sunit Γ' Δ →
    Γ ⊢ χ →
    Δ ⊢ tr →
      Γ' ⊢ χ
| trE :
      sunit ⊢ tr
| arrI {φ : Typ P} :
    Γ; φ ⊢ ψ →
      Γ ⊢ [bi| φ → ψ ]
| arrE :
    Γ ⊢ [bi| φ → ψ ] →
    Δ ⊢ φ →
      Γ; Δ ⊢ ψ
| andI :
    Γ ⊢ φ →
    Δ ⊢ ψ →
      Γ; Δ ⊢ [bi| φ ∧ ψ ]
| andE {φ ψ : Typ P} :
    BunchSubtreeSubst Γ (φ; ψ) Γ' Δ  →
    Γ ⊢ χ →
    Δ ⊢ [bi| φ ∧ ψ ] →
      Γ' ⊢ χ
| orI1 :
    Γ ⊢ φ₁ →
      Γ ⊢ [bi| φ₁ ∨ φ₂]
| orI2 :
    Γ ⊢ φ₂ →
      Γ ⊢ [bi| φ₁ ∨ φ₂]
| orE {φ ψ : Typ P} :
    BunchSubtreeSubst Δ φ Δ' ψ →
    BunchSubtreeSubst Δ φ Δ'' Γ →
    Γ ⊢ [bi| φ ∨ ψ ] →
    Δ ⊢ χ →
    Δ' ⊢ χ →
      Δ'' ⊢ χ
| flsE :
    Γ ⊢ fls →
      Γ ⊢ φ

namespace Entails

attribute [simp]
  id equiv weaken contract
  empI empE dandyI dandyE starI starE
  trI trE arrI arrE andI andE orI1 orI2 orE flsE

theorem id_admissible {φ : Typ P} : φ ⊢ φ := by
  induction φ <;> aesop

theorem cut_admissible {Γφ ΓΔ Δ : Bunch P} {φ : Typ P}
    (hΓ : BunchSubtreeSubst ΓΔ Δ Γφ φ)
  : Γφ ⊢ ψ → Δ ⊢ φ →
    ΓΔ ⊢ ψ
  := by
  intro h1 h2
  induction h2;
  stop
