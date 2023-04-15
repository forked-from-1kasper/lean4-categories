import Categories.Proto

set_option autoImplicit false

namespace Mathematics

structure Functor (A B : Category) :=
(apply : A.obj → B.obj)
(map   : Π {a b : A.obj}, Hom A a b → Hom B (apply a) (apply b))
(idm   : Π x, @map x x 1 = 1)
(com   : Π {a b c : A.obj} (f : Hom A b c) (g : Hom A a b), map (f ∘ g) = map f ∘ map g)

instance (A B : Category) : CoeFun (Functor A B) (λ _, A.obj → B.obj) :=
⟨Functor.apply⟩

lemma Functor.eq {A B : Category} {F G : Functor A B} (h₁ : F.apply = G.apply) (h₂ : HEq (@Functor.map A B F) (@Functor.map A B G)) : F = G :=
begin cases F; cases G; simp at h₁ h₂; subst h₁; subst h₂; rfl end

def idfun (C : Category) : Functor C C :=
{ apply := id,
  map   := id,
  idm   := λ _, rfl,
  com   := λ _ _, rfl }

def comfun {A B C : Category} (F : Functor B C) (G : Functor A B) : Functor A C :=
{ apply := λ x, F (G x),
  map   := λ g, F.map (G.map g),
  idm   := by { intros; dsimp; rw [G.idm, F.idm] },
  com   := by { intros; dsimp; rw [G.com, F.com] } }

def Δ {A : Category} (B : Category) (b : B.obj) : Functor A B :=
{ apply := λ _, b,
  map   := λ _, B.id b,
  idm   := λ _, rfl,
  com   := λ _ _, Eq.symm (B.lid _) }

section
  lemma Functor.lid {A B : Category} (F : Functor A B) : comfun (idfun B) F = F := rfl
  lemma Functor.rid {A B : Category} (F : Functor A B) : comfun F (idfun A) = F := rfl
  lemma Functor.assoc {A B C D : Category} (F : Functor C D) (G : Functor B C) (H : Functor A B) : comfun F (comfun G H) = comfun (comfun F G) H := rfl
end

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

def Algebra {C : Category} (F : Functor C C) :=
Σ (c : C.obj), Hom C (F c) c

def Algebra.hom {C : Category} {F : Functor C C} (Γ₁ Γ₂ : Algebra F) :=
{ φ : Hom C Γ₁.1 Γ₂.1 // φ ∘ Γ₁.2 = Γ₂.2 ∘ F.map φ }

def Algebra.idhom {C : Category} {F : Functor C C} (Γ : Algebra F) : Algebra.hom Γ Γ :=
⟨1, begin rw [F.idm]; apply Eq.trans; apply C.lid; apply Eq.symm (C.rid _) end⟩

def Algebra.com {C : Category} {F : Functor C C} {Γ₁ Γ₂ Γ₃ : Algebra F}
  (φ : Algebra.hom Γ₂ Γ₃) (ψ : Algebra.hom Γ₁ Γ₂) : Algebra.hom Γ₁ Γ₃ :=
⟨φ.1 ∘ ψ.1, by rw [C.assoc, ψ.2, ←C.assoc, φ.2, C.assoc, F.com]⟩

section
  variable {C : Category} {F : Functor C C}

  lemma Algebra.lid {Γ₁ Γ₂ : Algebra F} (φ : Algebra.hom Γ₁ Γ₂) : Algebra.com (Algebra.idhom Γ₂) φ = φ :=
  begin apply Subtype.eq; apply C.lid end

  lemma Algebra.rid {Γ₁ Γ₂ : Algebra F} (φ : Algebra.hom Γ₁ Γ₂) : Algebra.com φ (Algebra.idhom Γ₁) = φ :=
  begin apply Subtype.eq; apply C.rid end

  lemma Algebra.assoc {Γ₁ Γ₂ Γ₃ Γ₄ : Algebra F} (φ : Algebra.hom Γ₃ Γ₄) (ψ : Algebra.hom Γ₂ Γ₃) (ρ : Algebra.hom Γ₁ Γ₂) :
    Algebra.com (Algebra.com φ ψ) ρ = Algebra.com φ (Algebra.com ψ ρ) :=
  begin apply Subtype.eq; apply C.assoc end
end

def Algebra.category {C : Category} (F : Functor C C) : Category :=
{ obj   := Algebra F,
  hom   := Algebra.hom,
  id    := Algebra.idhom,
  com   := Algebra.com,
  lid   := Algebra.lid,
  rid   := Algebra.rid,
  assoc := Algebra.assoc }

notation "𝐴𝑙𝑔𝑒𝑏𝑟𝑎" => Algebra.category

def Simplex : Category :=
{ obj   := ℕ,
  hom   := λ n m, Functor (𝚫 n) (𝚫 m),
  id    := λ k, idfun (𝚫 k),
  com   := comfun,
  lid   := Functor.lid,
  rid   := Functor.rid,
  assoc := Functor.assoc }

notation:100 "𝚫" => Simplex