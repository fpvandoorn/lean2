
import ..move_to_lib
open function eq

namespace pushout
  section


  structure three_by_three_span : Type :=
    {A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : Type}
    {f₁₀ : A₂₀ -> A₀₀} {f₃₀ : A₂₀ -> A₄₀}
    {f₁₂ : A₂₂ -> A₀₂} {f₃₂ : A₂₂ -> A₄₂}
    {f₁₄ : A₂₄ -> A₀₄} {f₃₄ : A₂₄ -> A₄₄}
    {f₀₁ : A₀₂ -> A₀₀} {f₀₃ : A₀₂ -> A₀₄}
    {f₂₁ : A₂₂ -> A₂₀} {f₂₃ : A₂₂ -> A₂₄}
    {f₄₁ : A₄₂ -> A₄₀} {f₄₃ : A₄₂ -> A₄₄}
    (s₁₁ : f₀₁ o f₁₂ == f₁₀ o f₂₁) (s₃₁ : f₄₁ o f₃₂ == f₃₀ o f₂₁)
    (s₁₃ : f₀₃ o f₁₂ == f₁₄ o f₂₃) (s₃₃ : f₄₃ o f₃₂ == f₃₄ o f₂₃)

  open three_by_three_span
  variable (E : three_by_three_span)
Definition pushout2hv (E : three_by_three_span) : Type :=
  pushout (pushout.functor (f₂₁ E) (f₀₁ E) (f₄₁ E) (s₁₁ E) (s₃₁ E))
          (pushout.functor (f₂₃ E) (f₀₃ E) (f₄₃ E) (s₁₃ E) (s₃₃ E))

Definition pushout2vh (E : three_by_three_span) : Type :=
  pushout (pushout.functor (f₁₂ E) (f₁₀ E) (f₁₄ E) (s₁₁ E)^-1ʰᵗʸ (s₁₃ E)^-1ʰᵗʸ)
          (pushout.functor (f₃₂ E) (f₃₀ E) (f₃₄ E) (s₃₁ E)^-1ʰᵗʸ (s₃₃ E)^-1ʰᵗʸ)

Definition three_by_three (E : three_by_three_span) : pushout2hv E <~> pushout2vh E := sorry

Defined.
Defined. pushout
