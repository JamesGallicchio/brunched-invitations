import BunchImpl.Bunch

namespace BunchImpl

open Bunch

/-- `Subbunch B b` iff `b` is a subtree of `B` -/
inductive Subbunch {P : Sort u} : Bunch P → Bunch P → Prop
| refl : Subbunch b b
| commaL : Subbunch BL b → Subbunch (BL,ᵇ BR) b
| commaR : Subbunch BR b → Subbunch (BL,ᵇ BR) b
| semiL : Subbunch BL b → Subbunch (BL;ᵇ BR) b
| semiR : Subbunch BR b → Subbunch (BL;ᵇ BR) b

namespace Subbunch

attribute [refl] refl
attribute [simp] refl commaL commaR semiL semiR

theorem comma_inv :
  Subbunch (BL,ᵇ BR) b ↔
    Subbunch BL b ∨ Subbunch BR b ∨ b = (BL,ᵇ BR) := by
  constructor
  · intro h; cases h <;> simp_all
  · intro h; cases h <;> aesop

theorem semi_inv :
  Subbunch (BL;ᵇ BR) b ↔
    Subbunch BL b ∨ Subbunch BR b ∨ b = (BL;ᵇ BR) := by
  constructor
  · intro h; cases h <;> simp_all
  · intro h; cases h <;> aesop

theorem trans : Subbunch b1 b2 → Subbunch b2 b3 → Subbunch b1 b3 := by
  intro h1 h2
  induction h1 <;> cases h2 <;> simp_all

theorem size_lt {B1 : Bunch P} : Subbunch B1 b1 → sizeOf B1 ≥ sizeOf b1 := by
  intro h1
  induction h1 <;> simp <;> linarith
