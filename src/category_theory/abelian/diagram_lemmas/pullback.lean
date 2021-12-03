import category_theory.abelian.pseudoelements

noncomputable theory

open category_theory (hiding comp_apply)
open category_theory.abelian.pseudoelement
open category_theory.limits

universes v u

variables {V : Type u} [category.{v} V] [abelian V]

local attribute [instance] preadditive.has_equalizers_of_has_kernels
local attribute [instance] object_to_sort hom_to_fun
local attribute [instance] category_theory.abelian.pseudoelement.setoid

open_locale pseudoelement zero_object

namespace pullback_diagram

variables {x y z : V}
variables {k : x ⟶ z} {h : y ⟶ z}


/--
    kernel snd  --ι--> pullback k h ---snd---> y
        |                |                     |
        |               fst                    h
        |                |                     |
        v                v                     v
    kernel k -------ι--> x ------k-----------> z
-/


lemma aux1 : (kernel.ι pullback.snd ≫ @pullback.fst V _ x y z k h _) ≫ k = 0 :=
begin
  rw [category.assoc, pullback.condition, ←category.assoc, kernel.condition, zero_comp],
end

#check kernel.lift k (kernel.ι pullback.snd ≫ @pullback.fst V _ x y z k h _) aux1

instance is_iso : is_iso (kernel.lift k (kernel.ι pullback.snd ≫ @pullback.fst V _ x y z k h _) aux1) := sorry

end pullback_diagram

namespace pushout_diagram

variables {w x y : V}
variables {g : w ⟶ x} {f : w ⟶ y}

#check @pushout.inl V _ _ _ _ f g _

/--
w ----f----> y -----------π--> cokernel f
|            |
g            inl
|            |
v            v
x ---inr---> pushout -----π--> cokernel inr

-/

lemma aux2 : (f ≫ @pushout.inl V _ _ _ _ f g _)  ≫ cokernel.π pushout.inr = 0 :=
begin
  rw [pushout.condition, category.assoc, cokernel.condition, comp_zero],
end

instance is_iso : is_iso (cokernel.desc (f ≫ @pushout.inl V _ _ _ _ f g _) (cokernel.π pushout.inr) aux2)
  := sorry

end pushout_diagram
