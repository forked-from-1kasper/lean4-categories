import Categories.Colimit
import Categories.Comma

set_option autoImplicit false

namespace Mathematics

-- https://ncatlab.org/nlab/show/cobordism+category
-- https://people.math.umass.edu/~weston/oldpapers/cobord.pdf

-- we do not require existence of all coproducts here,
-- but require that for φ : ∂ A + ∂ B ≅ ∂ (A + B)
-- we have φ ∘ inl (∂ A) (∂ B) = ∂ (inl A B) (and so on for “inr”)

-- possible lack of all coproducts leaves some flexibility, because, for example,
-- if we require all manifolds to have some fixed (for each manifold) dimension,
-- then there will be no coproducts of manifolds with different dimensions,
-- while we still can form category with all continuous maps between them

-- also note that there is no initial object in such C iff it is empty
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

  def Cob.left  {a b : C.obj} (φ : Cob Γ a b) := φ.1
  def Cob.right {a b : C.obj} (φ : Cob Γ a b) := φ.2.1

  def Cob.iso {a b : C.obj} (φ : Cob Γ a b) : a + ∂ Γ φ.left ≅ b + ∂ Γ φ.right := φ.2.2

  def Cob.refl (a : C.obj) : Cob Γ a a :=
  ⟨a, a, Iso.refl _⟩

  def Cob.symm {a b : C.obj} (φ : Cob Γ a b) : Cob Γ b a :=
  ⟨φ.2.1, φ.1, Iso.symm φ.2.2⟩

  -- probably there should be easier way to obtain this isomorphism
  def Cob.trans {a b c : C.obj} (φ : Cob Γ a b) (ψ : Cob Γ b c) : Cob Γ a c :=
  ⟨φ.1 + ψ.1, φ.2.1 + ψ.2.1, coproductApLeft (semiadditiveIso Γ.additive.1)⁻¹
                           ⬝ coproductAssoc _ _ _
                           ⬝ coproductApRight φ.2.2
                           ⬝ (coproductAssoc _ _ _)⁻¹
                           ⬝ coproductApLeft (coproductComm _ _)
                           ⬝ coproductAssoc _ _ _
                           ⬝ coproductApRight ψ.2.2
                           ⬝ (coproductAssoc _ _ _)⁻¹
                           ⬝ coproductApLeft ((coproductComm _ _)⁻¹ ⬝ semiadditiveIso Γ.additive.1)⟩

  def Cob.boundary {a b : C.obj} (φ : Cob Γ a b) : ∂ Γ a ≅ ∂ Γ b :=
    (coproductInitialLeft _ _ (Γ.square φ.1))⁻¹ ⬝ semiadditiveIso Γ.additive.1
  ⬝ functorIso _ φ.2.2 ⬝ (semiadditiveIso Γ.additive.1)⁻¹ ⬝ coproductInitialLeft _ _ (Γ.square _)

  def Cob.idem (m : C.obj) : Cob Γ (∂ Γ m) (∂ Γ (∂ Γ m)) :=
  ⟨∂ Γ m, m, coproductInitialLeft _ _ (Γ.square m) ⬝ (coproductInitialRight _ _ (Γ.square m))⁻¹⟩
end

def Cob.isomorphism {C : Category} [HasCoproducts C] {Γ : Cobordism C} {a b : C.obj} (φ ψ : Cob Γ a b) :=
{ w : φ.1 ≅ ψ.1 × φ.2.1 ≅ ψ.2.1 // madd 1 ((∂ Γ).map w.2.1) ∘ φ.2.2.1 = ψ.2.2.1 ∘ madd 1 ((∂ Γ).map w.1.1) }

def Cob.isorefl {C : Category} [HasCoproducts C] {Γ : Cobordism C} {a b : C.obj} (φ : Cob Γ a b) : Cob.isomorphism φ φ :=
⟨(Iso.refl _, Iso.refl _), begin
                             show madd 1 (Γ.boundary.map 1) ∘ _ = _ ∘ madd 1 (Γ.boundary.map 1);
                             rw [Γ.boundary.idm, Γ.boundary.idm]; apply Eq.trans;
                             apply congrArg (· ∘ _); apply maddId; apply Eq.symm;
                             apply Eq.trans; apply congrArg; apply maddId;
                             apply Eq.trans; apply C.rid; apply Eq.symm (C.lid _)
                           end⟩

def isClosed {C : Category} (Γ : Cobordism C) (m : C.obj) := ∂ Γ m ≅ ∂ Γ (∂ Γ m)
def bounds {C : Category} [HasCoproducts C] (Γ : Cobordism C) (m : C.obj) := Cob Γ m (∂ Γ (∂ Γ m))

def boundaryInital {C : Category} (Γ : Cobordism C) {x : C.obj} (H : isInitial C x) : isInitial C (∂ Γ x) :=
begin apply initialIso (Γ.square (∂ Γ x)); apply functorIso; apply initialUniq; apply Γ.square; exact H end

def boundaryInitialIso {C : Category} (Γ : Cobordism C) {x : C.obj} (H : isInitial C x) : ∂ Γ x ≅ x :=
begin apply initialUniq; apply boundaryInital Γ H; exact H end

def boundaryZero {C : Category} [HasInitial C] (Γ : Cobordism C) : ∂ Γ 0 ≅ 0 :=
boundaryInitialIso Γ HasInitial.property

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
  ⟨λ w, ⟨((HasColimits.property _ w.cone).val,
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

  instance : HasInitial (𝐶𝑜𝑐𝑜𝑛𝑒 J C) :=
  { ε        := Cocone.zero 0,
    property := Cocone.hasInitial }

  instance : HasCoproducts (𝐶𝑜𝑐𝑜𝑛𝑒 J C) :=
  { μ        := Cocone.add,
    inl      := Cocone.inl,
    inr      := Cocone.inr,
    property := Cocone.hasCoproducts }

  def boundaryAdditive : @isAdditive (𝐶𝑜𝑐𝑜𝑛𝑒 J C) (𝐶𝑜𝑐𝑜𝑛𝑒 J C) boundary :=
  begin
    apply additiveCriteria _ _ _ _ _;
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
      { apply Subtype.eq; funext _; apply (HasInitial.property _).prop } };
    { apply Cocone.iso _ _ _ _; apply colimDelta; apply Sigma.mk _ _;
      apply Natural.initial; exists Natural.initial _; constructor <;>
      { apply Subtype.eq; funext; apply (HasInitial.property _).prop };
      { intro; apply (HasInitial.property _).prop };
      { intro; apply (HasInitial.property _).prop } }
  end

  -- this is generalization of an example linked below
  -- https://mathoverflow.net/a/59696
  def Cocone.cobord : Cobordism (𝐶𝑜𝑐𝑜𝑛𝑒 J C) :=
  { boundary := boundary,
    ι        := boundaryNat,
    square   := boundarySquare,
    additive := boundaryAdditive }
end

section
  variable {C : Category} [HasInitial C]

  def Cobordism.trivial : Cobordism C :=
  { boundary := Δ C 0,
    ι        := Natural.initial 1,
    square   := λ _, HasInitial.property,
    additive :=
    begin
      constructor;
      intro a b c i j H x f₁ f₂; exists (HasInitial.property _).inh; constructor;
      { constructor <;> apply (HasInitial.property _).prop };
      intros; apply (HasInitial.property _).prop;
      intro o H; apply HasInitial.property
    end }
end
