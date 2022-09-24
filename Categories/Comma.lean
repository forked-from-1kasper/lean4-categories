import Categories.Functor

set_option autoImplicit false

namespace Mathematics

section
  variable {A B C : Category}

  def Comma.obj (F : Functor A C) (G : Functor B C) := Σ (a : A.obj) (b : B.obj), Hom C (F a) (G b)

  variable {F : Functor A C} {G : Functor B C}

  def Comma.mor (w₁ w₂ : Comma.obj F G) :=
  { w : Hom A w₁.1 w₂.1 × Hom B w₁.2.1 w₂.2.1 // w₂.2.2 ∘ F.map w.1 = G.map w.2 ∘ w₁.2.2 }

  def Comma.id (w : Comma.obj F G) : Comma.mor w w :=
  ⟨(1, 1), begin rw [F.idm, G.idm]; apply Eq.trans; apply C.rid; apply Eq.symm (C.lid _) end⟩

  def Comma.com {w₁ w₂ w₃ : Comma.obj F G} (f : Comma.mor w₂ w₃) (g : Comma.mor w₁ w₂) : Comma.mor w₁ w₃ :=
  ⟨(f.1.1 ∘ g.1.1, f.1.2 ∘ g.1.2), by rw [F.com, G.com, ←C.assoc, f.2, C.assoc, g.2, C.assoc]⟩

  lemma Comma.lid {w₁ w₂ : Comma.obj F G} (f : Comma.mor w₁ w₂) : Comma.com (Comma.id w₂) f = f :=
  begin apply Subtype.eq; apply Prod.eq; apply A.lid; apply B.lid end

  lemma Comma.rid {w₁ w₂ : Comma.obj F G} (f : Comma.mor w₁ w₂) : Comma.com f (Comma.id w₁) = f :=
  begin apply Subtype.eq; apply Prod.eq; apply A.rid; apply B.rid end

  lemma Comma.assoc {w₁ w₂ w₃ w₄ : Comma.obj F G} (f : Comma.mor w₃ w₄) (g : Comma.mor w₂ w₃) (h : Comma.mor w₁ w₂) :
    Comma.com (Comma.com f g) h = Comma.com f (Comma.com g h) :=
  begin apply Subtype.eq; apply Prod.eq; apply A.assoc; apply B.assoc end
end

def Comma {A B C : Category} (F : Functor A C) (G : Functor B C) : Category :=
{ obj   := Comma.obj F G,
  hom   := Comma.mor,
  id    := Comma.id,
  com   := Comma.com,
  lid   := Comma.lid,
  rid   := Comma.rid,
  assoc := Comma.assoc }

infix:61 " ↓ " => Comma