import category_theory.abelian.basic

open category_theory
open category_theory.abelian
open category_theory.limits

open_locale zero_object

variables {𝒞 : Type*} [category 𝒞] [abelian 𝒞]

variables {A B K' : 𝒞} {f : A ⟶ B} {ι' : K' ⟶ A}
variables (eq_zero : ι' ≫ f = 0)
include eq_zero

example : ∃(u : K' ⟶ kernel f), (u ≫ kernel.ι f = ι') :=
begin
  use kernel.lift f ι' eq_zero,
  rw kernel.lift_ι,
end
