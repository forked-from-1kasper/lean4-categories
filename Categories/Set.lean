import Categories.Proto

set_option autoImplicit false
universe u

namespace Mathematics

def Set : Category :=
{ obj   := Type u,
  hom   := λ A B, A → B,
  id    := @id,
  com   := Function.comp,
  lid   := λ _, rfl,
  rid   := λ _, rfl,
  assoc := λ _ _ _, rfl }