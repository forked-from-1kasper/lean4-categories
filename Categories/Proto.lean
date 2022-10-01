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

def ExistsUnique {A : Type u} (P : A → Prop) :=
{ x : A // P x ∧ ∀ y, P y → x = y }

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

def Opposite (C : Category) : Category :=
{ obj   := C.obj,
  hom   := λ a b, C.hom b a,
  id    := C.id,
  com   := λ f g, C.com g f,
  lid   := C.rid,
  rid   := C.lid,
  assoc := λ f g h, Eq.symm (C.assoc h g f) }

postfix:max "ᵒᵖ" => Opposite

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