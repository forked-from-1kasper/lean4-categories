import Categories.Proto

set_option autoImplicit false
universe u

namespace Mathematics

section
  variable (A : Sort u)

  def isProp := ∀ (a b : A), a = b

  structure isContr :=
  (inh : A) (prop : isProp A)
end

section
  variable (C : Category) (x : C.obj)

  def isInitial  := ∀ a, isContr (Hom C x a)
  def isTerminal := isInitial Cᵒᵖ x
end

def initialIso {C : Category} {a b : C.obj} (H₁ : isInitial C a) (φ : a ≅ b) : isInitial C b :=
begin intro x; constructor; exact (H₁ _).inh ∘ φ.2.1; intro f g; apply isoEpic φ; apply (H₁ _).prop end

def initialUniq {C : Category} {a b : C.obj} (H₁ : isInitial C a) (H₂ : isInitial C b) : a ≅ b :=
begin exists (H₁ _).inh; exists (H₂ _).inh; constructor; apply (H₂ _).prop; apply (H₁ _).prop end

class HasInitial (C : Category) :=
(ε : C.obj) (property : isInitial C ε)

instance (C : Category) [H : HasInitial C] : OfNat C.obj 0 := ⟨H.ε⟩

class HasTerminal (C : Category) :=
(τ : C.obj) (property : isTerminal C τ)

instance (C : Category) [H : HasTerminal C] : OfNat C.obj 1 := ⟨H.τ⟩
