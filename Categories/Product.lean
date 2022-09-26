import Categories.Functor

set_option autoImplicit false

namespace Mathematics

section
  variable (C : Category) {a b c : C.obj}

  def isProduct (π₁ : Hom C c a) (π₂ : Hom C c b) :=
  ∀ (x : C.obj) (f₁ : Hom C x a) (f₂ : Hom C x b), ∃! (f : Hom C x c), π₁ ∘ f = f₁ ∧ π₂ ∘ f = f₂

  def isCoproduct (i : Hom C a c) (j : Hom C b c) :=
  isProduct Cᵒᵖ i j
end

class HasCoproducts (C : Category) :=
(μ        : C.obj → C.obj → C.obj)
(inl      : Π x y, Hom C x (μ x y))
(inr      : Π x y, Hom C y (μ x y))
(property : Π x y, isCoproduct C (inl x y) (inr x y))

instance (C : Category) [H : HasCoproducts C] : Add C.obj := ⟨H.μ⟩
open HasCoproducts (inl inr)

namespace HasCoproducts
  variable {C : Category} [HasCoproducts C] {a b c : C.obj} (f : Hom C a c) (g : Hom C b c)

  def recur : Hom C (a + b) c :=
  (HasCoproducts.property a b c f g).val

  def recurβ₁ : recur f g ∘ inl a b = f :=
  (HasCoproducts.property a b c f g).property.left.left

  def recurβ₂ : recur f g ∘ inr a b = g :=
  (HasCoproducts.property a b c f g).property.left.right

  def uniq : ∀ (φ : Hom C (a + b) c), φ ∘ inl a b = f → φ ∘ inr a b = g → recur f g = φ :=
  λ _ h₁ h₂, (HasCoproducts.property _ _ _ _ _).property.right _ (And.intro h₁ h₂)

  def prop : ∀ (φ ψ : Hom C (a + b) c), φ ∘ inl a b = f → φ ∘ inr a b = g → ψ ∘ inl a b = f → ψ ∘ inr a b = g → φ = ψ :=
  begin intros; apply Eq.trans; apply Eq.symm; repeat { apply uniq <;> assumption } end

  def comm {d : C.obj} (h : Hom C c d) : recur (h ∘ f) (h ∘ g) = h ∘ recur f g :=
  begin apply uniq <;> rw [C.assoc]; rw [recurβ₁]; rw [recurβ₂] end
end HasCoproducts

section
  variable {C : Category} [HasCoproducts C] {a₁ a₂ b₁ b₂ : C.obj} (f : Hom C a₁ a₂) (g : Hom C b₁ b₂)

  def madd : Hom C (a₁ + b₁) (a₂ + b₂) :=
  HasCoproducts.recur (inl _ _ ∘ f) (inr _ _ ∘ g)

  lemma maddInl : madd f g ∘ inl a₁ b₁ = inl a₂ b₂ ∘ f :=
  HasCoproducts.recurβ₁ _ _

  lemma maddInr : madd f g ∘ inr a₁ b₁ = inr a₂ b₂ ∘ g :=
  HasCoproducts.recurβ₂ _ _
end

lemma maddId {C : Category} [HasCoproducts C] (a b : C.obj) : madd (C.id a) (C.id b) = 1 :=
begin apply HasCoproducts.uniq <;> rw [C.rid] <;> apply C.lid end

theorem maddCom {C : Category} [HasCoproducts C] {a₁ a₂ a₃ b₁ b₂ b₃ : C.obj}
  (f₁ : Hom C a₂ a₃) (g₁ : Hom C b₂ b₃) (f₂ : Hom C a₁ a₂) (g₂ : Hom C b₁ b₂) :
  madd f₁ g₁ ∘ madd f₂ g₂ = madd (f₁ ∘ f₂) (g₁ ∘ g₂) :=
begin
  apply Eq.symm; apply HasCoproducts.uniq;
  { apply Eq.trans; apply C.assoc; rw [maddInl, ←C.assoc, maddInl]; apply C.assoc };
  { apply Eq.trans; apply C.assoc; rw [maddInr, ←C.assoc, maddInr]; apply C.assoc }
end

theorem maddRec {C : Category} [HasCoproducts C] {a₁ a₂ b₁ b₂ c : C.obj}
  (f : Hom C a₁ a₂) (g : Hom C b₁ b₂) (φ : Hom C a₂ c) (ψ : Hom C b₂ c) :
  HasCoproducts.recur φ ψ ∘ madd f g = HasCoproducts.recur (φ ∘ f) (ψ ∘ g) :=
begin
  apply Eq.symm; apply HasCoproducts.uniq <;> rw [C.assoc];
  rw [maddInl, ←C.assoc, HasCoproducts.recurβ₁];
  rw [maddInr, ←C.assoc, HasCoproducts.recurβ₂]
end

section
  variable {A B : Category} [HasCoproducts B] (F G : Functor A B)

  def Functor.add : Functor A B :=
  { apply := λ i, F i + G i,
    map   := λ φ, madd (F.map φ) (G.map φ),
    idm   := begin
               intros; apply (HasCoproducts.property _ _ _ _ _).property.right; constructor;
               { rw [F.idm]; apply Eq.trans; apply B.lid; apply Eq.symm; apply B.rid };
               { rw [G.idm]; apply Eq.trans; apply B.lid; apply Eq.symm; apply B.rid }
             end,
    com   := begin
               intros; apply (HasCoproducts.property _ _ _ _ _).property.right; constructor;
               { rw [F.com]; apply Eq.trans; apply B.assoc; simp [*];
                 rw [maddInl, ←B.assoc, maddInl]; apply B.assoc };
               { rw [G.com]; apply Eq.trans; apply B.assoc; simp [*];
                 rw [maddInr, ←B.assoc, maddInr]; apply B.assoc }
             end }

  def Natural.inl : Natural F (Functor.add F G) :=
  ⟨λ _, HasCoproducts.inl _ _, λ _, Eq.symm (maddInl _ _)⟩

  def Natural.inr : Natural G (Functor.add F G) :=
  ⟨λ _, HasCoproducts.inr _ _, λ _, Eq.symm (maddInr _ _)⟩

  variable {H : Functor A B} (η : Natural F H) (ε : Natural G H)

  def Natural.recur : Natural (Functor.add F G) H :=
  ⟨λ x, HasCoproducts.recur (η x) (ε x),
   begin
     intros a b f; apply Eq.trans; apply maddRec; apply HasCoproducts.uniq;
     rw [B.assoc, HasCoproducts.recurβ₁, η.property];
     rw [B.assoc, HasCoproducts.recurβ₂, ε.property]
   end⟩

  def Natural.recurβ₁ : Natural.vert (Natural.recur F G η ε) (Natural.inl F G) = η :=
  begin apply Subtype.eq; funext _; apply HasCoproducts.recurβ₁ end

  def Natural.recurβ₂ : Natural.vert (Natural.recur F G η ε) (Natural.inr F G) = ε :=
  begin apply Subtype.eq; funext _; apply HasCoproducts.recurβ₂ end

  def Natural.uniq (φ : Natural (Functor.add F G) H) (h₁ : vert φ (inl F G) = η) (h₂ : vert φ (inr F G) = ε) : Natural.recur F G η ε = φ :=
  begin apply Subtype.eq; funext _; subst h₁; subst h₂; apply HasCoproducts.uniq <;> rfl end
end

def isAdditive {A B : Category} (F : Functor A B) :=
∀ (a b c : A.obj) (i : Hom A a c) (j : Hom A b c), isCoproduct A i j → isCoproduct B (F.map i) (F.map j)

def coproductIso {C : Category} {a b c₁ c₂ : C.obj} (f₁ : Hom C a c₁) (g₁ : Hom C b c₁) (f₂ : Hom C a c₂) (g₂ : Hom C b c₂)
  (φ : c₁ ≅ c₂) : φ.1 ∘ f₁ = f₂ → φ.1 ∘ g₁ = g₂ → isCoproduct C f₁ g₁ → isCoproduct C f₂ g₂ :=
begin
  intro H₁ H₂ H c h₁ h₂; apply Subtype.mk _ _;
  { apply _ ∘ φ.2.1; apply (H _ h₁ h₂).1 }; constructor;
  { constructor <;> show C.com _ _ = _;
    { rw [C.assoc, ←isoInterchange₁ H₁]; apply (H _ _ _).2.1.1 };
    { rw [C.assoc, ←isoInterchange₁ H₂]; apply (H _ _ _).2.1.2 } };
  { intro y G; apply isoEpic φ; rw [C.assoc, φ.2.2.2];
    apply Eq.trans (C.rid _); apply (H _ _ _).2.2;
    constructor <;> show C.com _ _ = _ <;> rw [C.assoc];
    { rw [H₁]; apply G.1 }; { rw [H₂]; apply G.2 } }
end

def coproductUniq {C : Category} {a b c₁ c₂ : C.obj} (f₁ : Hom C a c₁) (g₁ : Hom C b c₁)
  (f₂ : Hom C a c₂) (g₂ : Hom C b c₂) : isCoproduct C f₁ g₁ → isCoproduct C f₂ g₂ → c₁ ≅ c₂ :=
begin
  intro H₁ H₂; exists (H₁ c₂ f₂ g₂).1; exists (H₂ c₁ f₁ g₁).1; constructor;
  { apply Eq.trans; apply Eq.symm; apply (H₂ c₂ f₂ g₂).2.2; constructor;
    { apply Eq.trans; apply C.assoc; apply Eq.trans; apply congrArg;
      apply (H₂ c₁ f₁ g₁).2.1.1; apply (H₁ _ _ _).2.1.1 };
    { apply Eq.trans; apply C.assoc; apply Eq.trans; apply congrArg;
      apply (H₂ c₁ f₁ g₁).2.1.2; apply (H₁ _ _ _).2.1.2 };
    apply (H₂ c₂ f₂ g₂).2.2; constructor <;> apply C.lid };
  { apply Eq.trans; apply Eq.symm; apply (H₁ c₁ f₁ g₁).2.2; constructor;
    { apply Eq.trans; apply C.assoc; apply Eq.trans; apply congrArg;
      apply (H₁ c₂ f₂ g₂).2.1.1; apply (H₂ _ _ _).2.1.1 };
    { apply Eq.trans; apply C.assoc; apply Eq.trans; apply congrArg;
      apply (H₁ c₂ f₂ g₂).2.1.2; apply (H₂ _ _ _).2.1.2 };
    apply (H₁ c₁ f₁ g₁).2.2; constructor <;> apply C.lid }
end

def additiveCriteria {A B : Category} [HasCoproducts A] [HasCoproducts B]
  (F : Functor A B) (H : ∀ x y, F x + F y ≅ F (x + y))
  (G₁ : ∀ x y, (H x y).1 ∘ inl (F x) (F y) = F.map (inl x y))
  (G₂ : ∀ x y, (H x y).1 ∘ inr (F x) (F y) = F.map (inr x y)) : isAdditive F :=
begin
  intro a b c i j G; apply coproductIso (inl _ _) (inr _ _) (F.map i) (F.map j) _ _ _ _;
  apply Iso.trans; apply H; apply functorIso; apply coproductUniq;
  apply HasCoproducts.property; apply G;
  { apply Eq.trans; apply B.assoc; rw [G₁ a b];
    apply Eq.trans; apply Eq.symm (F.com _ _);
    apply congrArg; apply HasCoproducts.recurβ₁ };
  { apply Eq.trans; apply B.assoc; rw [G₂ a b];
    apply Eq.trans; apply Eq.symm (F.com _ _);
    apply congrArg; apply HasCoproducts.recurβ₂ };
  apply HasCoproducts.property
end

def additiveIso {A B : Category} [HasCoproducts A] [HasCoproducts B] {F : Functor A B}
  (H : isAdditive F) {x y : A.obj} : F x + F y ≅ F (x + y) :=
begin apply coproductUniq; apply HasCoproducts.property; apply H; apply HasCoproducts.property end

def coproductSymm {C : Category} [HasCoproducts C] (a b : C.obj) : a + b ≅ b + a :=
begin
  exists HasCoproducts.recur (inr b a) (inl b a);
  exists HasCoproducts.recur (inr a b) (inl a b);
  constructor <;>
  { apply HasCoproducts.prop;
    { show _ = inl _ _; rw [C.assoc, HasCoproducts.recurβ₁, HasCoproducts.recurβ₂] };
    { show _ = inr _ _; rw [C.assoc, HasCoproducts.recurβ₂, HasCoproducts.recurβ₁] };
    repeat { apply C.lid } };
end

def coproductAssoc {C : Category} [HasCoproducts C] (a b c : C.obj) : a + (b + c) ≅ (a + b) + c :=
begin
  exists HasCoproducts.recur (inl _ _ ∘ inl _ _) (HasCoproducts.recur (inl _ _ ∘ inr _ _) (inr _ _));
  exists HasCoproducts.recur (HasCoproducts.recur (inl _ _) (inr _ _ ∘ inl _ _)) (inr _ _ ∘ inr _ _); constructor;
  { apply HasCoproducts.prop;
    { show _ = inl _ _; rw [C.assoc, HasCoproducts.recurβ₁]; apply HasCoproducts.prop;
      { show _ = inl _ _ ∘ inl _ _; rw [C.assoc, HasCoproducts.recurβ₁]; apply HasCoproducts.recurβ₁ };
      { show _ = inl _ _ ∘ inr _ _; rw [C.assoc, HasCoproducts.recurβ₂, ←C.assoc, HasCoproducts.recurβ₂]; apply HasCoproducts.recurβ₁ }; rfl; rfl };
    { show _ = inr _ _; rw [C.assoc, HasCoproducts.recurβ₂, ←C.assoc, HasCoproducts.recurβ₂, HasCoproducts.recurβ₂] };
    repeat { apply C.lid } };
  { apply HasCoproducts.prop;
    { show _ = inl _ _; rw [C.assoc, HasCoproducts.recurβ₁, ←C.assoc, HasCoproducts.recurβ₁, HasCoproducts.recurβ₁] };
    { show _ = inr _ _; rw [C.assoc, HasCoproducts.recurβ₂]; apply HasCoproducts.prop;
      { show _ = inr _ _ ∘ inl _ _; rw [C.assoc, HasCoproducts.recurβ₁, ←C.assoc, HasCoproducts.recurβ₁]; apply HasCoproducts.recurβ₂ };
      { show _ = inr _ _ ∘ inr _ _; rw [C.assoc, HasCoproducts.recurβ₂] apply HasCoproducts.recurβ₂ }; rfl; rfl };
  repeat { apply C.lid } }
end

def coproductApLeft {C : Category} [HasCoproducts C] {a b c : C.obj} (H : a ≅ b) : c + a ≅ c + b :=
begin
  exists madd (C.id c) H.1; exists madd (C.id c) H.2.1; constructor;
  { rw [maddCom, C.lid, H.2.2.1]; apply maddId };
  { rw [maddCom, C.lid, H.2.2.2]; apply maddId }
end

def coproductApRight {C : Category} [HasCoproducts C] {a b c : C.obj} (H : a ≅ b) : a + c ≅ b + c :=
begin
  exists madd H.1 (C.id c); exists madd H.2.1 (C.id c); constructor;
  { rw [maddCom, C.lid, H.2.2.1]; apply maddId };
  { rw [maddCom, C.lid, H.2.2.2]; apply maddId }
end