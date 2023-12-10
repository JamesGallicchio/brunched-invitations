import BunchImpl.Typ

namespace BunchImpl

open Typ

/-- Bunches, the contexts of bunched logic. -/
inductive Bunch.X (P : Sort u) (V : Sort v)
| prop : V → Typ P → Bunch.X P V
| cunit : Bunch.X P V
| comma : Bunch.X P V → Bunch.X P V → Bunch.X P V
| sunit : Bunch.X P V
| semi : Bunch.X P V → Bunch.X P V → Bunch.X P V
deriving Inhabited, DecidableEq

def Bunch (P : Sort u) : Type u := ∀ V : Sort u, Bunch.X P V

namespace Bunch

instance : Coe (Bunch P) (Bunch.X P V) := ⟨(· V)⟩

noncomputable instance {P : Sort u} : SizeOf (Bunch P) where
  sizeOf b := sizeOf (b PUnit)

def cunit : Bunch P := fun _ => .cunit
def comma (l r : Bunch P) : Bunch P := fun _ => .comma (l _) (r _)
def sunit : Bunch P := fun _ => .sunit
def semi (l r : Bunch P) : Bunch P := fun _ => .semi (l _) (r _)

scoped infixr:40 " ,ᵇ " => Bunch.comma
scoped infixr:40 " ;ᵇ " => Bunch.semi

@[simp] theorem comma_app {b1 b2 : Bunch P}
  : (b1 ,ᵇ b2) V = .comma (b1 V) (b2 V) := rfl

@[simp] theorem semi_app {b1 b2 : Bunch P}
  : (b1 ;ᵇ b2) V = .semi (b1 V) (b2 V) := rfl

@[simp] theorem cunit_neq_sunit : @cunit P ≠ sunit    := fun h => nomatch (congrFun h PUnit)
@[simp] theorem cunit_neq_comma : cunit    ≠ (l ,ᵇ r) := fun h => nomatch (congrFun h PUnit)
@[simp] theorem cunit_neq_semi  : cunit    ≠ (l ;ᵇ r) := fun h => nomatch (congrFun h PUnit)
@[simp] theorem sunit_neq_cunit : @sunit P ≠ cunit    := fun h => nomatch (congrFun h PUnit)
@[simp] theorem sunit_neq_comma : sunit    ≠ (l ,ᵇ r) := fun h => nomatch (congrFun h PUnit)
@[simp] theorem sunit_neq_semi  : sunit    ≠ (l ;ᵇ r) := fun h => nomatch (congrFun h PUnit)
@[simp] theorem comma_neq_cunit : (l ,ᵇ r) ≠ cunit    := fun h => nomatch (congrFun h PUnit)
@[simp] theorem comma_neq_sunit : (l ,ᵇ r) ≠ sunit    := fun h => nomatch (congrFun h PUnit)
@[simp] theorem comma_neq_semi  : (l1 ,ᵇ r1) ≠ (l2 ;ᵇ r2) := fun h => nomatch (congrFun h PUnit)
@[simp] theorem semi_neq_cunit  : (l ;ᵇ r) ≠ cunit    := fun h => nomatch (congrFun h PUnit)
@[simp] theorem semi_neq_sunit  : (l ;ᵇ r) ≠ sunit    := fun h => nomatch (congrFun h PUnit)
@[simp] theorem semi_neq_comma  : (l1 ;ᵇ r1) ≠ (l2 ,ᵇ r2) := fun h => nomatch (congrFun h PUnit)

@[simp] theorem comma_eq_comma : comma l1 r1 = comma l2 r2 ↔ l1 = l2 ∧ r1 = r2 := by
  constructor
  · intro h
    constructor <;> (funext V; have := congrFun h V; simp at this; simp [*])
  · rintro ⟨rfl,rfl⟩; rfl

@[simp] theorem semi_eq_semi : semi l1 r1 = semi l2 r2 ↔ l1 = l2 ∧ r1 = r2 := by
  constructor
  · intro h
    constructor <;> (funext V; have := congrFun h V; simp at this; simp [*])
  · rintro ⟨rfl,rfl⟩; rfl

@[simp] theorem neq_left_comma {P : Sort u} {b1 b2 : Bunch P}
  : (b1 ,ᵇ b2) ≠ b1 := by
  intro h
  have := congrArg sizeOf h
  clear h
  simp [instSizeOfBunch, comma] at this
  linarith

@[simp] theorem neq_right_comma
  : (b1 ,ᵇ b2) ≠ b2 := by
  intro h; have := congrArg sizeOf h; clear h
  simp [instSizeOfBunch, comma] at this

@[simp] theorem neq_self_left_comma
  : b1 ≠ (b1 ,ᵇ b2) := by
  intro h; have := congrArg sizeOf h; clear h
  simp [instSizeOfBunch, comma] at this
  linarith

@[simp] theorem neq_self_right_comma
  : b2 ≠ (b1 ,ᵇ b2) := by
  intro h; have := congrArg sizeOf h; clear h
  simp [instSizeOfBunch, comma] at this

@[simp] theorem neq_left_semi
  : (b1 ;ᵇ b2) ≠ b1 := by
  intro h; have := congrArg sizeOf h; clear h
  simp [instSizeOfBunch, semi] at this
  linarith

@[simp] theorem neq_right_semi
  : (b1 ;ᵇ b2) ≠ b2 := by
  intro h; have := congrArg sizeOf h; clear h
  simp [instSizeOfBunch, semi] at this

@[simp] theorem neq_self_left_semi
  : b1 ≠ (b1 ;ᵇ b2) := by
  intro h; have := congrArg sizeOf h; clear h
  simp [instSizeOfBunch, semi] at this
  linarith

@[simp] theorem neq_self_right_semi
  : b2 ≠ (b1 ;ᵇ b2) := by
  intro h; have := congrArg sizeOf h; clear h
  simp [instSizeOfBunch, semi] at this

end Bunch


inductive BunchWithHole.X (P : Sort u) (V : Sort v)
| hole
| commaL (l : X P V) (r : Bunch P)
| commaR (l : Bunch P) (r : X P V)
| semiL (l : X P V) (r : Bunch P)
| semiR (l : Bunch P) (r : X P V)

def BunchWithHole (P) := ∀ V, BunchWithHole.X P V

namespace BunchWithHole

open Bunch X

@[simp] def substX {P : Sort u} (b : Bunch.X P V) : BunchWithHole.X P V → Bunch.X P V
| .hole => b
| .commaL l r => .comma (substX b l) r
| .commaR l r => .comma l (substX b r)
| .semiL  l r => .semi (substX b l) r
| .semiR  l r => .semi l (substX b r)

def subst {P : Sort u} (b : Bunch P) (Γ : BunchWithHole P) : Bunch P :=
  fun V => substX (b V) (Γ V)

theorem sizeOf_pos (h : BunchWithHole.X P V) : sizeOf h > 0 := by
  induction h <;> simp

@[simp] theorem sizeOf_substX (b : Bunch.X P V) (h) :
    sizeOf (substX b h) = sizeOf b + sizeOf h - 1 := by
  induction h <;> simp [subst, substX, comma, semi, instSizeOfBunch] at * <;>
    simp [*] <;> sorry

@[simp] theorem substX_idem : substX b Γ = b ↔ Γ = .hole := by
  constructor
  · intro h; have := sizeOf_substX b Γ
    rw [h] at this
    rw [Nat.add_sub_assoc (sizeOf_pos _)] at this
    simp at this
    cases Γ <;> simp at * <;> (
      apply Nat.pos_iff_ne_zero.mp (sizeOf_pos _) this
    )
  · rintro rfl; rfl

@[simp] theorem idem_substX : b = substX b Γ ↔ Γ = .hole := by
  rw [eq_comm]
  simp

instance : FunLike (BunchWithHole.X P V) (Bunch.X P V) (fun _ => Bunch.X P V) where
  coe hole b := substX b hole
  coe_injective' := by
    intro Γ1 Γ2 h
    simp at h
    have : ∀ b, _ = _ := congrFun h
    clear h
    induction Γ1 generalizing Γ2 <;> (
      cases Γ2 <;> simp at this ⊢
    )
    repeat sorry

instance : FunLike (BunchWithHole P) (Bunch P) (fun _ => Bunch P) where
  coe hole b := subst b hole
  coe_injective' := sorry

@[simp] theorem hole_def : hole b = b := rfl
@[simp] theorem commaL_def : commaL l r b = (l b,ᵇ r) := rfl
@[simp] theorem commaR_def : commaR l r b = (l,ᵇ r b) := rfl
@[simp] theorem semiL_def  : semiL  l r b = (l b;ᵇ r) := rfl
@[simp] theorem semiR_def  : semiR  l r b = (l;ᵇ r b) := rfl

@[pp_dot, simp] def comp (Γ₁ Γ₂ : BunchWithHole P) : BunchWithHole P :=
  match Γ₁ with
  | hole => Γ₂
  | commaL l r => commaL (comp l Γ₂) r
  | commaR l r => commaR l (comp r Γ₂)
  | semiL  l r => semiL  (comp l Γ₂) r
  | semiR  l r => semiR  l (comp r Γ₂)

@[simp] theorem comp_hole (Γ : BunchWithHole P) : Γ.comp hole = Γ :=
  by induction Γ <;> simp_all

theorem comp_def (h1 h2 : BunchWithHole P) (b : Bunch P)
  : (h1.comp h2) b = h1 (h2 b) := by
  induction h1 <;>
    simp_all [comp, FunLike.coe, subst, substX] <;> (
    next ih =>
    funext V
    have := congrFun ih V
    rw [this]
  )

@[simp] theorem eq_prop (Γ : BunchWithHole P)
    : Γ b V = .prop v φ ↔ Γ = hole ∧ b V = .prop v φ := by
  cases Γ <;> simp [FunLike.coe, subst, substX]

@[simp] theorem prop_eq (Γ : BunchWithHole P)
    : .prop v φ = Γ b V ↔ Γ = hole ∧ b V = .prop v φ := by
  rw [eq_comm]
  simp

@[simp] theorem eq_cunit (Γ : BunchWithHole P)
    : Γ b = cunit ↔ Γ = hole ∧ b = cunit := by
  cases Γ <;> simp [FunLike.coe, subst] <;> (
    intro h
    have := congrFun h PUnit
    cases this
  )

@[simp] theorem cunit_eq (Γ : BunchWithHole P)
    : cunit = Γ b ↔ Γ = hole ∧ b = cunit := by
  rw [show (_ = _ ↔ _ = _) from ⟨Eq.symm, Eq.symm⟩]
  simp

@[simp] theorem eq_sunit (Γ : BunchWithHole P)
    : Γ b = sunit ↔ Γ = hole ∧ b = sunit := by
  cases Γ <;> simp [FunLike.coe, subst] <;> (
    intro h
    have := congrFun h PUnit
    cases this
  )

@[simp] theorem sunit_eq (Γ : BunchWithHole P)
    : sunit = Γ b ↔ Γ = hole ∧ b = sunit := by
  rw [show (_ = _ ↔ _ = _) from ⟨Eq.symm, Eq.symm⟩]
  simp

theorem eq_comma (Γ : BunchWithHole P)
    : Γ b = (Δ₁,ᵇ Δ₂) ↔
        Γ = hole ∧ b = (Δ₁,ᵇ Δ₂)
      ∨ (∃ Γ', Γ = .commaL Γ' Δ₂ ∧ Γ' b = Δ₁)
      ∨ (∃ Γ', Γ = .commaR Δ₁ Γ' ∧ Γ' b = Δ₂)
  := by
  cases Γ <;> aesop

theorem eq_semi (Γ : BunchWithHole P)
    : Γ b = (Δ₁;ᵇ Δ₂) ↔
        Γ = hole ∧ b = (Δ₁;ᵇ Δ₂)
      ∨ (∃ Γ', Γ = .semiL Γ' Δ₂ ∧ Γ' b = Δ₁)
      ∨ (∃ Γ', Γ = .semiR Δ₁ Γ' ∧ Γ' b = Δ₂)
  := by
  cases Γ <;> aesop

theorem eq_inv {Γ Γ' : BunchWithHole P} {φ φ' : Bunch P}
  : Γ φ = Γ' φ' → (∃ Δ, φ = Δ φ' ∧ Γ.comp Δ = Γ') ∨
                  (∃ Δ, φ' = Δ φ ∧ Γ'.comp Δ = Γ) ∨
      (∃ Δ Δ' : Bunch P → BunchWithHole P,
        Δ φ = Γ' ∧ Δ' φ' = Γ ∧
        ∀ ψ ψ', Δ ψ ψ' = Δ' ψ' ψ
      )
  := by
  intro h
  induction Γ generalizing Γ'
  case hole => simp_all
  case commaL ih | commaR ih | semiL ih | semiR ih =>
    simp at h
    rw [eq_comm] at h
    first | rw [eq_comma] at h | rw [eq_semi] at h
    rcases h with (⟨rfl,rfl⟩|⟨Γ'',rfl,h⟩|⟨Γ'',rfl,h⟩)
    · simp
    case inr.inl | inr.inr =>
      first
      | simp; rw [eq_comm] at h
        rcases ih h with (h1|h2|⟨Δ,Δ',rfl,rfl,h3⟩)
          <;> clear ih h
        · simp [h1]
        · simp [h2]
        · apply Or.inr; apply Or.inr
          iterate 2 (
            first | refine ⟨(fun x => commaL _ _),rfl,?_⟩
                  | refine ⟨(fun x => commaR _ _),rfl,?_⟩
                  | refine ⟨(fun x => semiL _ _),rfl,?_⟩
                  | refine ⟨(fun x => semiR _ _),rfl,?_⟩
          )
          intro ψ ψ'
          simp [h3]
      | cases h; simp
        iterate 2 (
          first | refine ⟨(fun x => commaL _ _),rfl,?_⟩
                | refine ⟨(fun x => commaR _ _),rfl,?_⟩
                | refine ⟨(fun x => semiL _ _),rfl,?_⟩
                | refine ⟨(fun x => semiR _ _),rfl,?_⟩
        )
        intro ψ ψ'
        simp

@[simp] theorem idem (Γ : BunchWithHole P) (b : Bunch P)
    : Γ b = b ↔ Γ = hole := by
  simp [FunLike.coe]

@[simp] theorem idem' (Γ : BunchWithHole P) (b : Bunch P)
    : b = Γ b ↔ Γ = hole := by
  simp [FunLike.coe]

end BunchWithHole

def Subbunch (B b : Bunch P) := ∃ Γ : BunchWithHole P, Γ b = B
