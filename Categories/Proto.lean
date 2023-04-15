import Categories.Notation

set_option autoImplicit false
universe u v w

theorem congr₂ {A : Sort u} {B : Sort v} {C : Sort w} {f : A → B → C} {a₁ a₂ : A} {b₁ b₂ : B} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ :=
h₁ ▸ h₂ ▸ rfl

theorem Sigma.eta {A : Type u} {B : A → Type v} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
  (h₁ : a₁ = a₂) (h₂ : HEq b₁ b₂) : Sigma.mk a₁ b₁ = Sigma.mk a₂ b₂ :=
begin subst h₁; subst h₂; rfl end

theorem Prod.eq {A : Type u} {B : Type v} {w₁ w₂ : A × B} (h₁ : w₁.1 = w₂.1) (h₂ : w₁.2 = w₂.2) : w₁ = w₂ :=
begin cases w₁; cases w₂; simp at h₁ h₂; subst h₁; subst h₂; rfl end

notation "⊥" => False
notation "⊤" => True
notation "𝟎" => Empty
notation "𝟏" => Unit
notation "★" => Unit.unit
notation "𝟐" => Bool
notation "ℕ" => Nat

instance : HAdd (Type u) (Type v) (Type (max u v)) := ⟨Sum⟩

def ExistsUnique {A : Type u} (P : A → Prop) :=
{ x : A // P x ∧ ∀ y, P y → x = y }

open Lean.TSyntax.Compat in
macro "∃! " xs:Lean.explicitBinders ", " b:term : term =>
  Lean.expandExplicitBinders ``ExistsUnique xs b

namespace Mathematics

structure Category :=
(obj   : Type u)
(hom   : obj → obj → Type v)
(id    : Π x, hom x x)
(com   : Π {a b c : obj}, hom b c → hom a b → hom a c)
(lid   : Π {a b : obj} (f : hom a b), com (id b) f = f)
(rid   : Π {a b : obj} (f : hom a b), com f (id a) = f)
(assoc : Π {a b c d : obj} (f : hom c d) (g : hom b c) (h : hom a b), com (com f g) h = com f (com g h))

abbrev Hom := Category.hom

instance (C : Category) (x : C.obj) : OfNat (Hom C x x) 1 := ⟨C.id x⟩
infix:70 (priority := high) " ∘ " => Category.com _

def Category.zero : Category :=
{ obj   := 𝟎,
  hom   := λ _ _, 𝟎,
  id    := λ x, nomatch x,
  com   := λ x _, nomatch x,
  lid   := λ x, nomatch x,
  rid   := λ x, nomatch x,
  assoc := λ x _ _, nomatch x }

notation "𝟘" => Category.zero

def Category.one : Category :=
{ obj   := 𝟏,
  hom   := λ _ _, 𝟏,
  id    := λ ★, ★,
  com   := λ _ _, ★,
  lid   := @λ ★ ★ ★ => rfl,
  rid   := @λ ★ ★ ★ => rfl,
  assoc := @λ ★ ★ ★ ★ ★ ★ ★ => rfl }

notation "𝟙" => Category.one

def Opposite (C : Category) : Category :=
{ obj   := C.obj,
  hom   := λ a b, C.hom b a,
  id    := C.id,
  com   := λ f g, C.com g f,
  lid   := C.rid,
  rid   := C.lid,
  assoc := λ f g h, Eq.symm (C.assoc h g f) }

postfix:max "ᵒᵖ" => Opposite

example (C : Category) : C = (Cᵒᵖ)ᵒᵖ := rfl

section
  variable {C : Category} {a b : C.obj} (f : Hom C a b)

  def monic := ∀ (t : C.obj) (h k : Hom C t a), f ∘ h = f ∘ k → h = k
  def epic  := ∀ (t : C.obj) (h k : Hom C b t), h ∘ f = k ∘ f → h = k

  def splitEpic  := { g : Hom C b a // f ∘ g = 1 }
  def splitMonic := { g : Hom C b a // g ∘ f = 1 }
end

def hasInv {C : Category} {a b : C.obj} (f : Hom C a b) :=
{ g : Hom C b a // f ∘ g = 1 ∧ g ∘ f = 1 }

def Iso {C : Category} (a b : C.obj) :=
Σ (f : Hom C a b), hasInv f

infix:60 " ≅ " => Iso

def Iso.refl {C : Category} (c : C.obj) : c ≅ c :=
begin exists 1; exists 1; constructor <;> apply C.lid end

def Iso.symm {C : Category} {a b : C.obj} : a ≅ b → b ≅ a :=
begin intro H; exists H.2.1; exists H.1; constructor; exact H.2.2.2; exact H.2.2.1 end

postfix:max "⁻¹" => Iso.symm

def hasInvCom {C : Category} {a b c : C.obj} {f : Hom C b c} {g : Hom C a b} :
  hasInv f → hasInv g → hasInv (f ∘ g) :=
begin
  intros H₁ H₂; exists H₂.1 ∘ H₁.1; constructor;
  { rw [C.assoc, ←C.assoc g, H₂.2.1]; apply Eq.trans;
    apply congrArg; apply C.lid; apply H₁.2.1 };
  { rw [C.assoc, ←C.assoc H₁.1, H₁.2.2]; apply Eq.trans;
    apply congrArg; apply C.lid; apply H₂.2.2 }
end

def Iso.trans {C : Category} {a b c : C.obj} : a ≅ b → b ≅ c → a ≅ c :=
begin intro H₁ H₂; exists H₂.1 ∘ H₁.1; apply hasInvCom; exact H₂.2; exact H₁.2 end

infixl:70 " ⬝ " => Iso.trans

def isoInterchange₁ {C : Category} {a b c : C.obj} {φ : b ≅ c} {f : Hom C a b} {g : Hom C a c} : φ.1 ∘ f = g → f = φ.2.1 ∘ g :=
begin intro H; rw [←C.lid f]; apply Eq.trans; apply congrArg (· ∘ f); apply Eq.symm φ.2.2.2; rw [C.assoc, H] end

def isoInterchange₂ {C : Category} {a b c : C.obj} {φ : b ≅ c} {f : Hom C a b} {g : Hom C a c} : f = φ.2.1 ∘ g → φ.1 ∘ f = g :=
begin intro H; rw [←C.lid g]; apply Eq.symm; apply Eq.trans; apply congrArg (· ∘ g); apply Eq.symm φ.2.2.1; rw [C.assoc, H] end

section
  variable {C : Category} {a b : C.obj} (φ : a ≅ b)

  def isoMono : monic φ.1 :=
  begin
    intro c h k H; rw [←C.lid h]; apply Eq.trans;
    apply congrArg (· ∘ h); apply Eq.symm φ.2.2.2;
    rw [C.assoc, H, ←C.assoc, φ.2.2.2]; apply C.lid
  end

  def isoEpic : epic φ.1 :=
  begin
    intro c h k H; rw [←C.rid h]; apply Eq.trans;
    apply congrArg; apply Eq.symm φ.2.2.1;
    rw [←C.assoc, H, C.assoc, φ.2.2.1]; apply C.rid
  end

  def isoMonoRev : monic φ.2.1 := isoMono φ⁻¹
  def isoEpicRev : epic φ.2.1  := isoEpic φ⁻¹
end

namespace Join
  variable (A B : Category)

  def mor := A.obj + B.obj

  def hom : mor A B → mor A B → Type (max _ _)
  | Sum.inl a, Sum.inl b => Hom A a b
  | Sum.inr _, Sum.inl _ => 𝟎
  | Sum.inl _, Sum.inr _ => 𝟏
  | Sum.inr a, Sum.inr b => Hom B a b

  def id : Π (x : mor A B), hom A B x x
  | Sum.inl x => A.id x
  | Sum.inr y => B.id y

  def com : Π {a b c : mor A B}, hom A B b c → hom A B a b → hom A B a c
  | Sum.inl _, Sum.inl _, Sum.inl _, f, g => A.com f g
  | Sum.inr _, Sum.inl _, Sum.inl _, _, ε => nomatch ε
  | Sum.inl _, Sum.inr _, Sum.inl _, ε, _ => nomatch ε
  | Sum.inr _, Sum.inr _, Sum.inl _, ε, _ => nomatch ε
  | Sum.inl _, Sum.inl _, Sum.inr _, _, _ => ★
  | Sum.inr _, Sum.inl _, Sum.inr _, _, ε => nomatch ε
  | Sum.inl _, Sum.inr _, Sum.inr _, _, _ => ★
  | Sum.inr _, Sum.inr _, Sum.inr _, f, g => B.com f g

  lemma lid : Π {a b : mor A B} (f : hom A B a b), com A B (id A B b) f = f
  | Sum.inl _, Sum.inl _, f => A.lid f
  | Sum.inr _, Sum.inl _, ε => nomatch ε
  | Sum.inl _, Sum.inr _, _ => rfl
  | Sum.inr _, Sum.inr _, g => B.lid g

  lemma rid : Π {a b : mor A B} (f : hom A B a b), com A B f (id A B a) = f
  | Sum.inl _, Sum.inl _, f => A.rid f
  | Sum.inr _, Sum.inl _, ε => nomatch ε
  | Sum.inl _, Sum.inr _, _ => rfl
  | Sum.inr _, Sum.inr _, g => B.rid g

  lemma assoc : Π {a b c d : mor A B} (f : hom A B c d) (g : hom A B b c) (h : hom A B a b), com A B (com A B f g) h = com A B f (com A B g h)
  | Sum.inl _, Sum.inl _, Sum.inl _, Sum.inl _, f, g, h => A.assoc f g h
  | Sum.inr _, Sum.inl _, Sum.inl _, Sum.inl _, _, _, ε => nomatch ε
  | Sum.inl _, Sum.inr _, Sum.inl _, Sum.inl _, _, ε, _ => nomatch ε
  | Sum.inr _, Sum.inr _, Sum.inl _, Sum.inl _, _, ε, _ => nomatch ε
  | Sum.inl _, Sum.inl _, Sum.inr _, Sum.inl _, ε, _, _ => nomatch ε
  | Sum.inr _, Sum.inl _, Sum.inr _, Sum.inl _, ε, _, _ => nomatch ε
  | Sum.inl _, Sum.inr _, Sum.inr _, Sum.inl _, ε, _, _ => nomatch ε
  | Sum.inr _, Sum.inr _, Sum.inr _, Sum.inl _, ε, _, _ => nomatch ε
  | Sum.inl _, Sum.inl _, Sum.inl _, Sum.inr _, _, _, _ => rfl
  | Sum.inr _, Sum.inl _, Sum.inl _, Sum.inr _, _, _, ε => nomatch ε
  | Sum.inl _, Sum.inr _, Sum.inl _, Sum.inr _, _, _, _ => rfl
  | Sum.inr _, Sum.inr _, Sum.inl _, Sum.inr _, _, ε, _ => nomatch ε
  | Sum.inl _, Sum.inl _, Sum.inr _, Sum.inr _, _, _, _ => rfl
  | Sum.inr _, Sum.inl _, Sum.inr _, Sum.inr _, _, _, ε => nomatch ε
  | Sum.inl _, Sum.inr _, Sum.inr _, Sum.inr _, _, _, _ => rfl
  | Sum.inr _, Sum.inr _, Sum.inr _, Sum.inr _, f, g, h => B.assoc f g h
end Join

def Join (A B : Category) : Category :=
{ obj   := A.obj + B.obj,
  hom   := Join.hom A B,
  id    := Join.id A B,
  com   := Join.com A B,
  lid   := Join.lid A B,
  rid   := Join.rid A B,
  assoc := Join.assoc A B }

def Category.cone (C : Category) := Join C 𝟙

def Simplex : ℕ → Category
|   0   => 𝟘
| n + 1 => Category.cone (Simplex n)

prefix:5 "𝚫 " => Simplex