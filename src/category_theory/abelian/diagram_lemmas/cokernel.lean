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

variables {A B C A' B' C' : V}

/--
```
A  ---f---> B ---g---> C ----> 0
|           |          |
α  (comm₁)  β  (comm₂) γ
|           |          |
v           v          v
A' ---f'--> B' --g'--> C'
```
-/

variables {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
variables {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'}
variables [exact f g] [epi g] [exact f' g']
variables (comm₁ : f ≫ β = α ≫ f') (comm₂ : g ≫ γ = β ≫ g')

include comm₁ comm₂

/--
```
      A  ---f---> B ---g---> C ----> 0
      |           |          |
      α  (comm₁)  β  (comm₂) γ
      |           |          |
      v           v          v
      A' ---f'--> B' --g'--> C'
      |           |          |
      π  (comm₃)  π  (comm₄) π
      |           |          |
      v           v          v
cokernel α -> cokernel β -> cokernel γ
           φ'            ψ'
```
-/

lemma aux1 : α ≫ (f' ≫ cokernel.π β) = 0 :=
begin
  rw [←category.assoc, ←comm₁, category.assoc, cokernel.condition, comp_zero],
end

lemma aux2 : β ≫ (g' ≫ cokernel.π γ) = 0 :=
begin
  rw [←category.assoc, ←comm₂, category.assoc, cokernel.condition, comp_zero],
end

def φ' : cokernel α ⟶ cokernel β := cokernel.desc _ _ (aux1 comm₁ comm₂)
def ψ' : cokernel β ⟶ cokernel γ := cokernel.desc _ _ (aux2 comm₁ comm₂)

lemma comm₃ : f' ≫ cokernel.π β = cokernel.π α ≫ (φ' comm₁ comm₂) :=
by rw [φ', cokernel.π_desc]

lemma comm₄ : g' ≫ cokernel.π γ = cokernel.π β ≫ (ψ' comm₁ comm₂) :=
by rw [ψ', cokernel.π_desc]

instance : exact (φ' comm₁ comm₂) (ψ' comm₁ comm₂) :=
⟨_, sorry⟩
