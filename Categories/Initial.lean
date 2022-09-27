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

class HasInitial (C : Category) :=
(ε : C.obj) (property : isInitial C ε)

instance (C : Category) [H : HasInitial C] : OfNat C.obj 0 := ⟨H.ε⟩

class HasTerminal (C : Category) :=
(τ : C.obj) (property : isTerminal C τ)

instance (C : Category) [H : HasTerminal C] : OfNat C.obj 1 := ⟨H.τ⟩