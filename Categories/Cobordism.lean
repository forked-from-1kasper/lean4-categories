import Categories.Colimit
import Categories.Comma

set_option autoImplicit false

namespace Mathematics

-- https://ncatlab.org/nlab/show/cobordism+category
-- https://people.math.umass.edu/~weston/oldpapers/cobord.pdf

-- we do not require existence of all coproducts here,
-- but require that for φ : ∂ A + ∂ B ≅ ∂ (A + B)
-- we have φ ∘ inl (∂ A) (∂ B) = ∂ (inl A B) (and so on for “inr”)
structure Cobordism (C : Category) :=
(boundary : Functor C C)
(ι        : Natural boundary 1)
(square   : ∀ x, isInitial C (boundary (boundary x)))
(additive : isAdditive boundary)

notation "∂" => Cobordism.boundary

def Cob {C : Category} [HasCoproducts C] (Γ : Cobordism C) (a b : C.obj) :=
Σ (u v : C.obj), a + ∂ Γ u ≅ b + ∂ Γ v

section
  variable {C : Category} [HasCoproducts C] (Γ : Cobordism C)

  def Cob.refl (a : C.obj) : Cob Γ a a :=
  ⟨a, a, Iso.refl _⟩

  def Cob.symm {a b : C.obj} (φ : Cob Γ a b) : Cob Γ b a :=
  ⟨φ.2.1, φ.1, Iso.symm φ.2.2⟩

  -- probably there should be easier way to obtain this isomorphism
  def Cob.trans {a b c : C.obj} (φ : Cob Γ a b) (ψ : Cob Γ b c) : Cob Γ a c :=
  ⟨φ.1 + ψ.1, φ.2.1 + ψ.2.1, coproductApLeft (additiveIso Γ.additive)⁻¹
                           ⬝ coproductAssoc _ _ _
                           ⬝ coproductApRight φ.2.2
                           ⬝ (coproductAssoc _ _ _)⁻¹
                           ⬝ coproductApLeft (coproductSymm _ _)
                           ⬝ coproductAssoc _ _ _
                           ⬝ coproductApRight ψ.2.2
                           ⬝ (coproductAssoc _ _ _)⁻¹
                           ⬝ coproductApLeft ((coproductSymm _ _)⁻¹ ⬝ additiveIso Γ.additive)⟩
end

def Cob.isomorphism {C : Category} [HasCoproducts C] {Γ : Cobordism C} {a b : C.obj} (φ ψ : Cob Γ a b) :=
{ w : φ.1 ≅ ψ.1 × φ.2.1 ≅ ψ.2.1 // madd 1 ((∂ Γ).map w.2.1) ∘ φ.2.2.1 = ψ.2.2.1 ∘ madd 1 ((∂ Γ).map w.1.1) }

section
  variable {J C : Category} [HasInitial C] [HasColimits J C]

  open HasColimits (colim)

  def boundaryApply (c : Cocone J C) : Cocone J C :=
  ⟨(Δ C 0, colim c.1.1), ⟨λ _, (HasInitial.property _).inh, λ _, (HasInitial.property _).prop _ _⟩⟩

  def boundaryMap {D₁ D₂ : Cocone J C} (f : Cocone.mor D₁ D₂) : Cocone.mor (boundaryApply D₁) (boundaryApply D₂) :=
  begin
    apply Subtype.mk _ _;
    { constructor;
      { apply HasColimits.recur D₁.1.1 ⟨_, _⟩; apply Subtype.mk _ _;
        { intro x; exact (HasColimits.cone D₂.1.1).val x ∘ f.1.2 x };
        { intro i j g; rw [C.assoc, f.1.2.2, ←C.assoc];
          apply congrArg (· ∘ _); apply (HasColimits.cone _).2 } };
      { apply Natural.id } };
    { intro; apply (HasInitial.property _).prop }
  end

  def boundary : Functor (𝐶𝑜𝑐𝑜𝑛𝑒 J C) (𝐶𝑜𝑐𝑜𝑛𝑒 J C) :=
  { apply := boundaryApply,
    map   := boundaryMap,
    idm   := begin
               intros; apply Subtype.eq; apply Prod.eq;
               { apply HasColimits.uniq _ _;
                 intro; apply Eq.trans; apply C.lid;
                 apply Eq.symm (C.rid _) };
               { rfl }
             end,
    com   := begin
               intros; apply Subtype.eq; apply congr₂;
               { apply HasColimits.uniq _ _; intro;
                 show C.com (C.com (Subtype.val _) (Subtype.val _)) _ = _;
                 rw [C.assoc, (HasColimits.property _ _).2.1,
                    ←C.assoc, (HasColimits.property _ _).2.1];
                 apply C.assoc };
               { apply Subtype.eq; funext _; apply (HasInitial.property _).prop }
             end }

  def boundarySquare : ∀ x, isInitial (𝐶𝑜𝑐𝑜𝑛𝑒 J C) (boundary (boundary x)) :=
  begin
    intro H N; constructor;
    { apply Subtype.mk (_, _) _; apply (colimZero HasInitial.property (HasColimits.property _) _).inh;
      apply Subtype.mk _ _; intros; apply (HasInitial.property _).inh;
      repeat { intros; apply (HasInitial.property _).prop } };
    { intro f g; apply Subtype.eq; apply Prod.eq;
      apply (colimZero HasInitial.property (HasColimits.property _) _).prop;
      apply Subtype.eq; funext _; apply (HasInitial.property _).prop }
  end

  def boundaryNat : @Natural (𝐶𝑜𝑐𝑜𝑛𝑒 J C) (𝐶𝑜𝑐𝑜𝑛𝑒 J C) boundary 1 :=
  ⟨λ w, ⟨((HasColimits.property _ ⟨w.1.2, w.2⟩).val,
         ⟨λ _, (HasInitial.property _).inh, λ _, (HasInitial.property _).prop _ _⟩),
          λ _, (HasInitial.property _).prop _ _⟩,
   begin
     intros a b f; apply Subtype.eq; apply Prod.eq;
     { show C.com (Subtype.val _) (Subtype.val _) = C.com f.1.1 (Subtype.val _);
       apply HasColimits.prop a.1.1 ⟨b.1.2, ⟨_, _⟩⟩ _ _ _ _;
       { intro x; exact f.1.1 ∘ a.2.1 x };
       { intro i j g; rw [C.assoc]; apply congrArg; apply a.2.2 };
       { intro x; rw [C.assoc]; apply Eq.trans;
         apply congrArg; apply HasColimits.recurβ;
         simp [*]; rw [←C.assoc]; apply Eq.trans; apply congrArg (· ∘ _);
         apply HasColimits.recurβ; apply Eq.symm; apply f.2 };
       { intro x; rw [C.assoc]; apply congrArg; apply HasColimits.recurβ } };
     { apply Subtype.eq; funext _; simp [*];
       apply (HasInitial.property _).prop }
   end⟩

  variable [HasCoproducts C]

  def Cocone.add (D₁ D₂ : Cocone J C) : Cocone J C :=
  ⟨(Functor.add D₁.1.1 D₂.1.1, D₁.1.2 + D₂.1.2), ⟨λ x, madd (D₁.2.val x) (D₂.2.val x),
   begin
     intros; simp [*]; apply Eq.trans; apply maddCom; apply congr₂;
     apply D₁.2.property; apply D₂.2.property
   end⟩⟩

  def Cocone.inl (D₁ D₂ : Cocone J C) : Cocone.mor D₁ (Cocone.add D₁ D₂) :=
  ⟨(HasCoproducts.inl _ _, Natural.inl _ _), λ _, Eq.symm (maddInl _ _)⟩

  def Cocone.inr (D₁ D₂ : Cocone J C) : Cocone.mor D₂ (Cocone.add D₁ D₂) :=
  ⟨(HasCoproducts.inr _ _, Natural.inr _ _), λ _, Eq.symm (maddInr _ _)⟩

  def Cocone.hasCoproducts (D₁ D₂ : Cocone J C) : isCoproduct (𝐶𝑜𝑐𝑜𝑛𝑒 J C) (Cocone.inl D₁ D₂) (Cocone.inr D₁ D₂) :=
  begin
    intro c f₁ f₂; apply Subtype.mk _ _;
    { apply Subtype.mk _ _; constructor;
      { apply HasCoproducts.recur f₁.1.1 f₂.1.1 };
      { apply Natural.recur _ _ f₁.1.2 f₂.1.2 };
      { intros; apply Eq.trans; apply maddRec;
        apply Eq.symm; apply Eq.trans; apply Eq.symm; apply HasCoproducts.comm;
        apply congr₂ <;> apply Eq.symm; apply f₁.2; apply f₂.2 } }; constructor;
    { constructor <;> apply Subtype.eq <;> apply Prod.eq;
      apply HasCoproducts.recurβ₁; apply Natural.recurβ₁;
      apply HasCoproducts.recurβ₂; apply Natural.recurβ₂ };
    { intro φ ⟨H₁, H₂⟩; apply Subtype.eq; subst H₁; subst H₂; apply Prod.eq;
      { apply HasCoproducts.uniq <;> rfl };
      { apply Natural.uniq <;> rfl } }
  end

  instance : HasCoproducts (𝐶𝑜𝑐𝑜𝑛𝑒 J C) :=
  { μ        := Cocone.add,
    inl      := Cocone.inl,
    inr      := Cocone.inr,
    property := Cocone.hasCoproducts }

  def boundaryAdditive : @isAdditive (𝐶𝑜𝑐𝑜𝑛𝑒 J C) (𝐶𝑜𝑐𝑜𝑛𝑒 J C) boundary :=
  begin
    apply additiveCriteria _ _ _ _;
    intro D₁ D₂; apply Cocone.iso _ _ _ _; apply colimAdd;
    { exists Natural.recur _ _ (Natural.id _) (Natural.id _); apply Subtype.mk (Natural.inl _ _);
      constructor <;> apply Subtype.eq <;> funext _;
      { apply (HasInitial.property _).prop };
      { apply HasCoproducts.prop;
        repeat { apply (HasInitial.property _).prop }
        repeat { apply (HasInitial.property _).inh } } };
    { intro; apply HasCoproducts.prop;
      repeat { apply (HasInitial.property _).prop }
      repeat { apply (HasInitial.property _).inh } };
    { intro; apply (HasInitial.property _).prop };
    { intro x y; apply Subtype.eq; apply Prod.eq;
      { apply HasColimits.prop x.1.1 ⟨_, _⟩;
        { intro; show C.com (C.com _ _) _ = _;
          apply Eq.trans; apply congrArg (· ∘ _);
          apply HasCoproducts.recurβ₁; apply HasColimits.recurβ };
        { intro; apply HasColimits.recurβ } };
      { apply Subtype.eq; funext _; apply (HasInitial.property _).prop } };
    { intro x y; apply Subtype.eq; apply Prod.eq;
      { apply HasColimits.prop y.1.1 ⟨_, _⟩;
        { intro; show C.com (C.com _ _) _ = _;
          apply Eq.trans; apply congrArg (· ∘ _);
          apply HasCoproducts.recurβ₂; apply HasColimits.recurβ };
        { intro; apply HasColimits.recurβ } };
      { apply Subtype.eq; funext _; apply (HasInitial.property _).prop } }
  end

  -- this is generalization of an example linked below
  -- https://mathoverflow.net/a/59696
  def Cocone.cobord : Cobordism (𝐶𝑜𝑐𝑜𝑛𝑒 J C) :=
  { boundary := boundary,
    ι        := boundaryNat,
    square   := boundarySquare,
    additive := boundaryAdditive }
end
