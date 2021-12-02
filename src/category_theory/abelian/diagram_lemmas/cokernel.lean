import category_theory.abelian.pseudoelements
import category_theory.abelian.opposite

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

lemma co_aux1 : α ≫ (f' ≫ cokernel.π β) = 0 :=
begin
  rw [←category.assoc, ←comm₁, category.assoc, cokernel.condition, comp_zero],
end

lemma co_aux2 : β ≫ (g' ≫ cokernel.π γ) = 0 :=
begin
  rw [←category.assoc, ←comm₂, category.assoc, cokernel.condition, comp_zero],
end

def φ' : cokernel α ⟶ cokernel β := cokernel.desc _ _ (co_aux1 comm₁ comm₂)
def ψ' : cokernel β ⟶ cokernel γ := cokernel.desc _ _ (co_aux2 comm₁ comm₂)

-- def φ' : cokernel α ⟶ cokernel β :=
-- begin
--   suffices : kernel β.op ⟶ kernel α.op,
--   exact (kernel_op_unop α).inv ≫ this.unop ≫ (kernel_op_unop β).hom,
--   have test := @φ Vᵒᵖ _ _
--     (opposite.op C') (opposite.op B') (opposite.op A')
--     (opposite.op C) (opposite.op B) (opposite.op A)
--     g'.op f'.op g.op f.op
--     γ.op β.op α.op (exact_op _ _),
-- end

lemma comm₃ : f' ≫ cokernel.π β = cokernel.π α ≫ (φ' comm₁ comm₂) :=
by rw [φ', cokernel.π_desc]

lemma comm₄ : g' ≫ cokernel.π γ = cokernel.π β ≫ (ψ' comm₁ comm₂) :=
by rw [ψ', cokernel.π_desc]

#check comm₄


lemma aux3_1 :
  (cokernel.π α) ≫ (φ' comm₁ comm₂) ≫ (ψ' comm₁ comm₂) =
  (f' ≫ g') ≫ (cokernel.π γ) :=
begin
  rw [←category.assoc, ←comm₃, category.assoc, ←comm₄, ←category.assoc],
end

lemma aux3_2 : (cokernel.π α) ≫ (φ' comm₁ comm₂) ≫ (ψ' comm₁ comm₂) = 0 :=
begin
  rw [aux3_1],
  convert zero_comp,
  exact exact.w,
end

lemma aux3 : (φ' comm₁ comm₂) ≫ (ψ' comm₁ comm₂) = 0 :=
begin
  have aux3_3 : (cokernel.π α) ≫ (φ' comm₁ comm₂) ≫ (ψ' comm₁ comm₂) = (cokernel.π α) ≫ 0,
  rw [aux3_2, comp_zero],
  haveI : epi (cokernel.π α) := by apply_instance,
  exact epi.left_cancellation _ _ aux3_3,
end

instance : exact (φ' comm₁ comm₂) (ψ' comm₁ comm₂) :=
begin
  apply exact_of_pseudo_exact, split,
  { rintros a, rw [←comp_apply, aux3, zero_apply], },
  { intros e1 he1,
    obtain ⟨e2, he2⟩ := @pseudo_surjective_of_epi V _ _ _ _ (cokernel.π β) (by apply_instance) e1,
    have he2_2 : (g' ≫ cokernel.π γ) e2 = 0,
    { rw [comm₄ comm₁ comm₂, comp_apply, he2, he1], },
    rw comp_apply at he2_2,

    obtain ⟨e3, he3⟩ := (@pseudo_exact_of_exact V _ _ _ _ _ γ (cokernel.π γ)
      (category_theory.abelian.exact_cokernel γ)).2 _ he2_2,

    obtain ⟨e4, he4⟩ := pseudo_surjective_of_epi g e3,
    have he4_1 := congr_arg γ he4,
    erw [he3, ←comp_apply, comm₂, comp_apply] at he4_1,

    obtain ⟨e5, he5_1, he5_2⟩ := sub_of_eq_image g' _ _ he4_1.symm,
    obtain ⟨e6, he6⟩ := (@pseudo_exact_of_exact V _ _ _ _ _ f' g' _).2 _ he5_1,

    use cokernel.π α e6,
    rw [←comp_apply, ←comm₃, comp_apply, he6, he5_2], assumption,

    rw [←comp_apply, cokernel.condition, zero_apply],
  }
end
