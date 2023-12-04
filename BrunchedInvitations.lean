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
deriving Inhabited

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
deriving Inhabited

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

theorem subtree_size_lt {B1 : Bunch P} : BunchSubtree B1 b1 → sizeOf B1 ≥ sizeOf b1 := by
  intro h1
  induction h1 <;> simp <;> linarith

end BunchSubtree

open Bunch in
inductive Path {P : Sort u} : Bunch P → Type u
| here : Path b1
| commaL : Path b1 → Path (b1, b2)
| commaR : Path b2 → Path (b1, b2)
| semiL : Path b1 → Path (b1; b2)
| semiR : Path b2 → Path (b1; b2)

namespace Path

instance : Inhabited (Path b) := ⟨.here⟩

/-- Get the bunch at the end of the `path` -/
def get {B : Bunch P} (path : Path B) : Bunch P :=
  match path with
  | .here => B
  | .commaL h
  | .commaR h
  | .semiL h
  | .semiR h => get h

@[simp] theorem get_cast (p : Path B) (h : B = B')
  : get (h ▸ p) = get p := by
  cases h; simp

theorem get_subtree (p : Path B) : BunchSubtree B p.get := by
  induction p <;> simp [get]
  case commaL => exact .commaL ‹_›
  case commaR => exact .commaR ‹_›
  case semiL => exact .semiL ‹_›
  case semiR => exact .semiR ‹_›

@[simp] theorem eq_here_of_get_eq (p : Path B) : p.get = B ↔ p = .here := by
  cases p <;> simp [get] <;> (
    next p =>
    have := p.get_subtree.subtree_size_lt
    intro h
    simp [h] at this
    try linarith
  )

def comp (p1 : Path B) (p2 : Path p1.get) : Path B :=
  match p1 with
  | .here => p2
  | .commaL h => .commaL <| comp h p2
  | .commaR h => .commaR <| comp h p2
  | .semiL h => .semiL <| comp h p2
  | .semiR h => .semiR <| comp h p2

@[simp] theorem get_comp (p1 : Path B) (p2 : Path p1.get) : get (p1.comp p2) = p2.get := by
  induction p1 <;> (simp [get] at p2; simp [comp])
    <;> (next ih => exact ih p2)

/-- `Subst p1 p2` iff `p1` and `p2` follow the same path &
are the same everywhere off the path -/
inductive Subst : {B1 B2 : Bunch P} → Path B1 → Path B2 → Prop
| here : Subst .here .here
| commaL (p1 : Path B1) (p2 : Path B2) (b) :
    Subst p1 p2 → Subst (.commaL (b2 := b) p1) (.commaL (b2 := b) p2)
| commaR (p1 : Path B1) (p2 : Path B2) (b) :
    Subst p1 p2 → Subst (.commaR (b1 := b) p1) (.commaR (b1 := b) p2)
| semiL (p1 : Path B1) (p2 : Path B2) (b) :
    Subst p1 p2 → Subst (.semiL (b2 := b) p1) (.semiL (b2 := b) p2)
| semiR (p1 : Path B1) (p2 : Path B2) (b) :
    Subst p1 p2 → Subst (.semiR (b1 := b) p1) (.semiR (b1 := b) p2)

@[simp] theorem subst_cast_left {B1 B1' B2 : Bunch P} (p1 : Path B1) (p2 : Path B2)
    (h1 : B1 = B1')
  : Subst (h1 ▸ p1) p2 ↔ Subst p1 p2 := by
  cases h1; simp

@[simp] theorem subst_cast_right {B1 B2 B2' : Bunch P} (p1 : Path B1) (p2 : Path B2)
    (h2 : B2 = B2')
  : Subst p1 (h2 ▸ p2) ↔ Subst p1 p2 := by
  cases h2; simp

theorem subst_comp (p11 : Path B1) (p12 : Path p11.get) (p21 : Path B2) (p22 : Path p21.get)
  : Subst p11 p21 → Subst p12 p22 → Subst (p11.comp p12) (p21.comp p22) := by
  intro h1 h2
  induction h1
  case here => simp [comp]; exact h2
  case commaL ih | commaR ih | semiL ih | semiR ih =>
    first | apply Subst.commaL | apply Subst.commaR | apply Subst.semiL | apply Subst.semiR
    apply ih
    assumption

@[simp] theorem here_inv (p : Path B') : Subst (.here : Path B) p ↔ p = .here := by
  cases p <;> (simp; try exact .here) <;> intro h <;> cases h

end Path


structure BunchWithHole (P : Sort u) where
  toFun : Bunch P → Bunch P
  path : ∀ b, Path (toFun b)
  get_path : ∀ b, (path b).get = b
  subst : ∀ b1 b2, Path.Subst (path b1) (path b2)

namespace BunchWithHole

attribute [pp_dot] toFun path subst

instance : CoeFun (BunchWithHole P) (λ _ => Bunch P → Bunch P) := ⟨toFun⟩

def id : BunchWithHole P where
  toFun := _root_.id
  path := fun _ => .here
  get_path := fun _ => rfl
  subst := fun _ _ => .here

@[simp] theorem id_def : id b = b := by
  simp [id, toFun]

@[pp_dot] def comp (Γ₁ Γ₂ : BunchWithHole P) : BunchWithHole P where
  toFun := Γ₁.toFun ∘ Γ₂.toFun
  path := fun b =>
    Path.comp (Γ₁.path (Γ₂ b)) (Γ₁.get_path _ ▸ Γ₂.path b)
  get_path := by simp [Γ₂.get_path]
  subst := fun b1 b2 => by
    simp
    apply Path.subst_comp
    · apply Γ₁.subst
    · simp; apply Γ₂.subst

theorem comp_def (h1 h2 : BunchWithHole P) (b : Bunch P)
  : (h1.comp h2) b = h1 (h2 b) := by
  simp [comp, toFun]

theorem subtree (Γ : BunchWithHole P) (b : Bunch P)
  : BunchSubtree (Γ b) b := by
  have := (Γ.path b).get_subtree
  rw [Γ.get_path] at this
  exact this

@[simp] theorem idem (Γ : BunchWithHole P) (b : Bunch P) : Γ b = b ↔ Γ = id := by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  rcases Γ with ⟨toFun, path, get_path, subst⟩
  simp at h
  suffices ∀ b', toFun b' = b' by
    have : toFun = _root_.id := funext this
    cases this
    simp [id]
    funext b
    have := get_path b
    simpa using this
  have hb : path b = .here := by
    have := Eq.trans (get_path b) h.symm; simpa using this
  intro b'
  have := subst b b'
  generalize hp : path b = p at hb this
  cases hb
  have get' := get_path b'
  simp_all [Path.get]

@[simp] theorem eq_prop (Γ : BunchWithHole P) : Γ b = .prop φ ↔ Γ = id ∧ b = .prop φ := by
  generalize hΓ : Γ b = B
  cases B <;> simp
  case cunit | comma | sunit | semi =>
    rintro rfl; simp [id] at hΓ; cases hΓ; simp
  case prop =>
    have := (Γ.path b).get_subtree
    rw [Γ.get_path, hΓ] at this
    cases this
    rw [idem] at hΓ
    simp [hΓ]

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
| subtree (h : BunchWithHole P) (b1 b2)
  : BunchPreEquiv b1 b2 → BunchPreEquiv (h b1) (h b2)

/-- Equivalence on bunches. -/
def BunchEquiv {P : Type u} : Bunch P → Bunch P → Prop :=
  EqvGen BunchPreEquiv

def BunchEquiv.is_equivalence : Equivalence (@BunchEquiv P) :=
  EqvGen.is_equivalence _

/- This gives access to `≈` notation on bunches. -/
instance : HasEquiv (Bunch P) := ⟨BunchEquiv⟩

theorem BunchEquiv.ofPre {b1 b2 : Bunch P} (h1 : BunchPreEquiv b1 b2) : b1 ≈ b2 :=
  EqvGen.rel _ _ h1

theorem BunchEquiv.trans {b1 b2 b3 : Bunch P} (h1 : b1 ≈ b2) (h2 : b2 ≈ b3) : b1 ≈ b3 :=
  EqvGen.trans _ _ _ h1 h2

theorem BunchEquiv.symm {b1 b2 : Bunch P} (h1 : b1 ≈ b2) : b2 ≈ b1 :=
  EqvGen.symm _ _ h1

theorem BunchEquiv.subtree (h : BunchWithHole P) (e : Γ ≈ Δ) : (h Γ ≈ h Δ) := by
  induction e with
  | rel _ _ h =>
    apply EqvGen.rel
    apply BunchPreEquiv.subtree
    exact h
  | refl =>
    exact .refl _
  | symm _ _ _ ih =>
    exact .symm ih
  | trans _ _ _ _ _ ih1 ih2 =>
    exact .trans ih1 ih2

set_option hygiene false in section
local infix:35 " ⊢ " => Entails

open Bunch in
inductive Entails {P : Type u} : Bunch P → Typ P → Prop
| id {φ : Typ P} :
      φ ⊢ φ
| equiv :
    Γ ≈ Δ →
    Γ ⊢ φ →
      Δ ⊢ φ
| weaken (Γ : BunchWithHole P) :
    Γ Δ ⊢ φ →
      Γ (Δ; Δ') ⊢ φ
| contract (Γ : BunchWithHole P) :
    Γ (Δ; Δ) ⊢ φ →
      Γ Δ ⊢ φ
| empI : cunit ⊢ emp
| empE (Γ : BunchWithHole P) :
    Γ cunit ⊢ χ   →
    Δ ⊢ emp →
      Γ Δ ⊢ χ
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
| starE {φ ψ : Typ P} (Γ : BunchWithHole P) :
    Γ (φ, ψ) ⊢ χ →
    Δ ⊢ [bi| φ * ψ ] →
      Γ Δ ⊢ χ
| trI (Γ : BunchWithHole P) :
    Γ sunit ⊢ χ →
    Δ ⊢ tr →
      Γ Δ ⊢ χ
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
    Γ ⊢ ψ →
      Γ ⊢ [bi| φ ∧ ψ ]
| andE {φ ψ : Typ P} (Γ : BunchWithHole P) :
    Γ (φ; ψ) ⊢ χ →
    Δ ⊢ [bi| φ ∧ ψ ] →
      Γ Δ ⊢ χ
| orI1 :
    Γ ⊢ φ₁ →
      Γ ⊢ [bi| φ₁ ∨ φ₂]
| orI2 :
    Γ ⊢ φ₂ →
      Γ ⊢ [bi| φ₁ ∨ φ₂]
| orE {φ₁ φ₂ : Typ P} (Γ : BunchWithHole P) (Δ : Bunch P):
    Δ ⊢ [bi| φ₁ ∨ φ₂ ] →
    Γ φ ⊢ χ →
    Γ ψ ⊢ χ →
      Γ Δ ⊢ χ
| flsE :
    Γ ⊢ fls →
      Γ ⊢ φ
end

scoped infix:35 " ⊢ " => Entails

namespace Entails

attribute [simp]
  id equiv weaken contract
  empI empE dandyI dandyE starI starE
  trI trE arrI arrE andI andE orI1 orI2 orE flsE

theorem id_admissible {φ : Typ P} : φ ⊢ φ := by
  induction φ <;> aesop

open Bunch in
theorem cut_admissible (Γ : BunchWithHole P) (Δ : Bunch P) (φ : Typ P)
  : Γ φ ⊢ ψ →
    Δ ⊢ φ →
      Γ Δ ⊢ ψ
  := by
  intro h1 h2
  generalize hΔ : Γ (prop φ) = Δ at h1
  induction h2
  case id =>
    exact hΔ ▸ h1
  case equiv h h1 ih =>
    refine Entails.equiv ?_ (ih hΔ)
    apply BunchEquiv.subtree _ h
  case weaken ih =>
    rw [←BunchWithHole.comp_def]
    apply Entails.weaken
    rw [BunchWithHole.comp_def]
    apply ih hΔ
  case contract ih =>
    rw [←BunchWithHole.comp_def]
    apply Entails.contract
    rw [BunchWithHole.comp_def]
    apply ih hΔ
  case empI =>
    induction h1
    case id =>
      simp at hΔ; rcases hΔ with ⟨rfl,rfl⟩
      simp
    repeat sorry
  repeat sorry
