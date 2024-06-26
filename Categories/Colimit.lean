import Categories.Product
import Categories.Initial

set_option autoImplicit false

namespace Mathematics

def isCocone {J C : Category} (F : Functor J C) (c : C.obj) :=
{ ψ : Π x, Hom C (F x) c // ∀ {i j : J.obj} (f : Hom J i j), ψ j ∘ F.map f = ψ i }

def Cocone.relative {J C : Category} (F : Functor J C) :=
Σ (c : C.obj), isCocone F c

notation F "-cocone" => Cocone.relative F

def isColimit {J C : Category} {F : Functor J C} (L : F-cocone) :=
∀ (N : F-cocone), ∃! (u : Hom C L.1 N.1), ∀ x, u ∘ L.2.val x = N.2.val x

def Cocone (J C : Category) :=
Σ (w : Functor J C × C.obj), isCocone w.1 w.2

def Cocone.cone {J C : Category} (L : Cocone J C) : L.1.1-cocone := ⟨L.1.2, L.2⟩

section
  variable {J C : Category}

  def Cocone.mor (D₁ D₂ : Cocone J C) :=
  { ε : Hom C D₁.1.2 D₂.1.2 × Natural D₁.1.1 D₂.1.1 // ∀ (i : J.obj), ε.1 ∘ D₁.2.val i = D₂.2.val i ∘ ε.2 i }

  def Cocone.id (D : Cocone J C) : Cocone.mor D D :=
  ⟨(C.id D.1.2, Natural.id D.1.1), λ _, begin simp [Natural.id]; rw [C.lid, C.rid] end⟩

  def Cocone.com {D₁ D₂ D₃ : Cocone J C} (f : Cocone.mor D₂ D₃) (g : Cocone.mor D₁ D₂) : Cocone.mor D₁ D₃ :=
  ⟨(f.1.1 ∘ g.1.1, Natural.vert f.1.2 g.1.2), λ x, begin rw [C.assoc, g.property x, ←C.assoc, f.property x]; apply C.assoc end⟩

  lemma Cocone.lid {D₁ D₂ : Cocone J C} (f : Cocone.mor D₁ D₂) : Cocone.com (Cocone.id D₂) f = f :=
  begin apply Subtype.eq; apply congr₂; apply C.lid; apply Natural.lid end

  lemma Cocone.rid {D₁ D₂ : Cocone J C} (f : Cocone.mor D₁ D₂) : Cocone.com f (Cocone.id D₁) = f :=
  begin apply Subtype.eq; apply congr₂; apply C.rid; apply Natural.rid end

  lemma Cocone.assoc {D₁ D₂ D₃ D₄ : Cocone J C} (f : Cocone.mor D₃ D₄) (g : Cocone.mor D₂ D₃) (h : Cocone.mor D₁ D₂) :
    Cocone.com (Cocone.com f g) h = Cocone.com f (Cocone.com g h) :=
  begin apply Subtype.eq; apply congr₂; apply C.assoc; apply Natural.assoc end
end

def Cocone.category (J C : Category) : Category :=
{ obj   := Cocone J C,
  hom   := Cocone.mor,
  id    := Cocone.id,
  com   := Cocone.com,
  lid   := Cocone.lid,
  rid   := Cocone.rid,
  assoc := Cocone.assoc }

notation "𝐶𝑜𝑐𝑜𝑛𝑒" => Cocone.category

class HasColimits (J C : Category) :=
(colim    : Functor J C → C.obj)
(cone     : ∀ F, isCocone F (colim F))
(property : ∀ F, isColimit ⟨colim F, cone F⟩)

open HasColimits (colim)

def Natural.initial {A B : Category} [HasInitial B] (F : Functor A B) : Natural (Δ B 0) F :=
⟨λ x, (HasInitial.property (F x)).inh, λ _, (HasInitial.property _).prop _ _⟩

def Cocone.zero {J C : Category} [HasInitial C] (x : C.obj) : Cocone J C :=
⟨(Δ C 0, x), ⟨λ _, (HasInitial.property x).inh, λ _, (HasInitial.property x).prop _ _⟩⟩

def Cocone.hasInitial {J C : Category} [HasInitial C] : isInitial (𝐶𝑜𝑐𝑜𝑛𝑒 J C) (Cocone.zero 0) :=
begin
  intro x; constructor; refine Subtype.mk ?_ ?_;
  { constructor; apply (HasInitial.property x.1.2).inh; apply Natural.initial };
  { intro i; apply (HasInitial.property _).prop };
  { intro f g; apply Subtype.eq; ext; apply (HasInitial.property _).prop;
    apply Subtype.eq; funext; apply (HasInitial.property _).prop }
end

def colimInitial {J C : Category} {F : Functor J C} {L : F-cocone} (H₁ : ∀ x, isInitial C (F x)) (H₂ : isColimit L) : isInitial C L.1 :=
begin
  intro c; let N : F-cocone := ⟨c, ⟨λ _, (H₁ _ _).inh, λ _, (H₁ _ _).prop _ _⟩⟩; constructor; apply (H₂ N).val;
  { intro f g; apply Eq.trans; apply Eq.symm; repeat { apply (H₂ N).property.right; intros; apply (H₁ _ _).prop } }
end

def colimZero {J C : Category} {ε : C.obj} {L : (@Δ J C ε)-cocone} (H₁ : isInitial C ε) (H₂ : isColimit L) : isInitial C L.1 :=
begin apply colimInitial; intro; apply H₁; exact H₂ end

def Cocone.initial {J C : Category} {L : Cocone J C} (H₁ : isInitial C L.1.2) (H₂ : ∀ x, isInitial C (L.1.1 x)) : isInitial (𝐶𝑜𝑐𝑜𝑛𝑒 J C) L :=
begin
  intro c; constructor; apply Subtype.mk (_, _) _; apply (H₁ _).inh;
  { apply Subtype.mk _ _; intro; apply (H₂ _ _).inh; intros; apply (H₂ _ _).prop };
  { intro; apply (H₂ _ _).prop };
  { intro f g; apply Subtype.eq; apply Prod.eq; apply (H₁ _).prop;
    apply Subtype.eq; funext _; apply (H₂ _ _).prop }
end

def Cocone.iso {J C : Category} {D₁ D₂ : Cocone J C} (φ : D₁.1.2 ≅ D₂.1.2) (ψ : Functor.iso D₁.1.1 D₂.1.1)
  (H : ∀ i, φ.1 ∘ D₁.2.1 i = D₂.2.1 i ∘ ψ.1.1 i) (G : ∀ i, φ.2.1 ∘ D₂.2.1 i = D₁.2.1 i ∘ ψ.2.1 i) : @Iso (𝐶𝑜𝑐𝑜𝑛𝑒 J C) D₁ D₂ :=
begin
  apply Sigma.mk _ _; { apply Subtype.mk (φ.1, ψ.1) _; intro; apply H };
  apply Subtype.mk _ _; { apply Subtype.mk (φ.2.1, ψ.2.1) _; intro; apply G };
  constructor <;> apply Subtype.eq <;> apply Prod.eq;
  apply φ.2.2.left; apply ψ.2.2.left; apply φ.2.2.right; apply ψ.2.2.right
end

namespace HasColimits
  variable {J C : Category} [HasColimits J C] (F : Functor J C) (L : F-cocone)

  def recur : Hom C (colim F) L.1 :=
  (HasColimits.property F L).1

  def recurβ : ∀ x, recur F L ∘ (cone F).1 x = L.2.1 x :=
  (HasColimits.property F L).2.1

  def uniq : ∀ (u : Hom C (colim F) L.1), (∀ x, u ∘ (cone F).1 x = L.2.1 x) → recur F L = u :=
  (HasColimits.property F L).2.2

  def prop (u₁ u₂ : Hom C (colim F) L.1) (h₁ : ∀ x, u₁ ∘ (cone F).1 x = L.2.1 x) (h₂ : ∀ x, u₂ ∘ (cone F).1 x = L.2.1 x) : u₁ = u₂ :=
  Eq.trans (Eq.symm (uniq F L u₁ h₁)) (uniq F L u₂ h₂)
end HasColimits

def colimitUniq {J C : Category} (F : Functor J C) (c₁ c₂ : F-cocone) : isColimit c₁ → isColimit c₂ → c₁.1 ≅ c₂.1 :=
begin
  intro h₁ h₂; exists (h₁ c₂).1; exists (h₂ c₁).1; constructor;
  { apply Eq.trans; apply Eq.symm; apply (h₂ c₂).2.2;
    { intro x; apply Eq.symm; apply Eq.trans; apply Eq.symm; apply (h₁ c₂).2.1 x;
      rw [C.assoc]; apply congrArg; apply Eq.symm; apply (h₂ c₁).2.1 };
    { apply (h₂ c₂).2.2; intro; apply C.lid } };
  { apply Eq.trans; apply Eq.symm; apply (h₁ c₁).2.2;
    { intro x; apply Eq.symm; apply Eq.trans; apply Eq.symm; apply (h₂ c₁).2.1 x;
      rw [C.assoc]; apply congrArg; apply Eq.symm; apply (h₁ c₂).2.1 };
    { apply (h₁ c₁).2.2; intros; apply C.lid } }
end

section
  variable {J C : Category} [HasCoproducts C] [HasColimits J C] (F G : Functor J C)

  def coneAdd : isCocone (Functor.add F G) (colim F + colim G) :=
  ⟨λ x, madd ((HasColimits.cone F).1 x) ((HasColimits.cone G).1 x),
   begin
     intros; apply Eq.trans; apply maddRec;
     apply congr₂ <;> rw [C.assoc] <;> apply congrArg;
     apply (HasColimits.cone F).2; apply (HasColimits.cone G).2
   end⟩

  open HasCoproducts (inl inr)

  def sumOfColimits : isColimit ⟨colim F + colim G, coneAdd F G⟩ :=
  begin
    intro N; apply Subtype.mk _ _;
    { apply HasCoproducts.recur;
      { apply HasColimits.recur F ⟨_, ⟨λ x, N.2.1 x ∘ inl _ _, _⟩⟩;
        intros i j f; rw [C.assoc, ←maddInl (F.map f) (G.map f), ←C.assoc];
        apply congrArg (· ∘ inl _ _); apply N.2.2 };
      { apply HasColimits.recur G ⟨_, ⟨λ x, N.2.1 x ∘ inr _ _, _⟩⟩;
        intros i j f; rw [C.assoc, ←maddInr (F.map f) (G.map f), ←C.assoc];
        apply congrArg (· ∘ inr _ _); apply N.2.2 } }; constructor;
    { intro x; apply Eq.trans; apply maddRec; apply HasCoproducts.uniq <;>
      apply Eq.symm <;> apply HasColimits.recurβ };
    { intro φ H; apply HasCoproducts.uniq <;> apply Eq.symm <;>
      apply HasColimits.uniq <;> intro x <;> simp [*] <;> rw [← H x] <;>
      rw [C.assoc, C.assoc] <;> apply congrArg <;> apply Eq.symm;
      apply maddInl; apply maddInr }
  end

  def colimAdd : colim F + colim G ≅ colim (Functor.add F G) :=
  colimitUniq (Functor.add F G)
    ⟨colim F + colim G, coneAdd F G⟩
    ⟨colim (Functor.add F G), HasColimits.cone _⟩
    (sumOfColimits F G) (HasColimits.property _)
end

def colimDelta {J C : Category} [HasInitial C] [HasColimits J C] : colim (J := J) (Δ C 0) ≅ 0 :=
begin
  apply initialUniq; apply colimInitial (F := Δ C 0) (L := ⟨colim _, HasColimits.cone _⟩);
  intro; apply HasInitial.property; apply HasColimits.property; apply HasInitial.property
end
