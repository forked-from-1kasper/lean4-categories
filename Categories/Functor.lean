import Categories.Proto

set_option autoImplicit false

namespace Mathematics

structure Functor (A B : Category) :=
(apply : A.obj → B.obj)
(map   : Π {a b : A.obj}, Hom A a b → Hom B (apply a) (apply b))
(idm   : Π x, @map x x 1 = 1)
(com   : Π {a b c : A.obj} (f : Hom A b c) (g : Hom A a b), map (f ∘ g) = map f ∘ map g)

lemma Functor.eq {A B : Category} (F G : Functor A B) (h₁ : F.apply = G.apply) (h₂ : HEq (@Functor.map A B F) (@Functor.map A B G)) : F = G :=
begin cases F; cases G; simp at h₁ h₂; subst h₁; subst h₂; rfl end

instance (A B : Category) : CoeFun (Functor A B) (λ _, A.obj → B.obj) :=
⟨Functor.apply⟩

def idfun (C : Category) : Functor C C :=
{ apply := id,
  map   := id,
  idm   := λ _, rfl,
  com   := λ _ _, rfl }

def Δ {A : Category} (B : Category) (b : B.obj) : Functor A B :=
{ apply := λ _, b,
  map   := λ _, B.id b,
  idm   := λ _, rfl,
  com   := λ _ _, Eq.symm (B.lid _) }

instance (C : Category) : OfNat (Functor C C) 1 := ⟨idfun C⟩

def Natural {A B : Category} (F G : Functor A B) :=
{ η : Π x, Hom B (F x) (G x) // Π {a b : A.obj} (f : Hom A a b), η b ∘ F.map f = G.map f ∘ η a }

instance (A B : Category) (F G : Functor A B) : CoeFun (Natural F G) (λ _, Π x, Hom B (F x) (G x)) :=
⟨Subtype.val⟩

def Natural.id {A B : Category} (F : Functor A B) : Natural F F :=
⟨λ x, B.id (F x), λ _, by rw [B.lid, B.rid]⟩

def Natural.vert {A B : Category} {F G H : Functor A B} (η : Natural G H) (μ : Natural F G) : Natural F H :=
⟨λ x, η x ∘ μ x, λ _, by rw [B.assoc, μ.property, ←B.assoc, η.property, B.assoc]⟩

section
  variable {A B : Category}

  lemma Natural.lid {F G : Functor A B} (η : Natural F G) : Natural.vert (Natural.id G) η = η :=
  begin apply Subtype.eq; funext _; apply B.lid end

  lemma Natural.rid {F G : Functor A B} (η : Natural F G) : Natural.vert η (Natural.id F) = η :=
  begin apply Subtype.eq; funext _; apply B.rid end

  lemma Natural.assoc {F G H K : Functor A B} (η : Natural H K) (μ : Natural G H) (ε : Natural F G) :
    Natural.vert (Natural.vert η μ) ε = Natural.vert η (Natural.vert μ ε) :=
  begin apply Subtype.eq; funext _; apply B.assoc end
end

def Natural.hasInv {A B : Category} {F G : Functor A B} (η : Natural F G) :=
{ ε : Natural G F // Natural.vert η ε = Natural.id G ∧ Natural.vert ε η = Natural.id F }

def Functor.iso {A B : Category} (F G : Functor A B) :=
Σ (η : Natural F G), η.hasInv

def Functor.category (A B : Category) : Category :=
{ obj   := Functor A B,
  hom   := Natural,
  id    := Natural.id,
  com   := Natural.vert,
  lid   := Natural.lid,
  rid   := Natural.rid,
  assoc := Natural.assoc }

instance : HPow Category Category Category := ⟨λ B A, Functor.category A B⟩

def functorIso {A B : Category} (F : Functor A B) {a b : A.obj} (f : a ≅ b) : F a ≅ F b :=
begin
  exists F.map f.1; exists F.map f.2.1; constructor;
  rw [←F.com, f.2.2.1, F.idm]; rw [←F.com, f.2.2.2, F.idm]
end