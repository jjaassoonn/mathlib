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

namespace kernel_diagram

variables {A B C A' B' C' : V}

/--
```
        A  ---f---> B ---g---> C
        |           |          |
        α  (comm₁)  β  (comm₂) γ
        |           |          |
        v           v          v
0 ----> A' ---f'--> B' --g'--> C'
```
-/

variables {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
variables {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'}
variables [exact f g] [mono f'] [exact f' g']
variables (comm₁ : f ≫ β = α ≫ f') (comm₂ : g ≫ γ = β ≫ g')

include comm₁ comm₂

/--
```           φ            ψ
    kernel α --> kernel β --> kernel γ
        |           |          |
        ι (comm₃)   ι (comm₄)  ι
        |           |          |
        v           v          v
        A  ---f---> B ---g---> C
        |           |          |
        α  (comm₁)  β  (comm₂) γ
        |           |          |
        v           v          v
0 ----> A' ---f'--> B' --g'--> C'
```
-/

lemma aux1 : (kernel.ι α ≫ f) ≫ β = 0 :=
begin
  rw [category.assoc, comm₁, ←category.assoc, kernel.condition, zero_comp],
end

lemma aux2 : (kernel.ι β ≫ g) ≫ γ = 0 :=
begin
  rw [category.assoc, comm₂, ←category.assoc, kernel.condition, zero_comp],
end


def φ : kernel α ⟶ kernel β := kernel.lift _ _ (aux1 comm₁ comm₂)
def ψ : kernel β ⟶ kernel γ := kernel.lift _ _ (aux2 comm₁ comm₂)


lemma comm₃ : (φ comm₁ comm₂) ≫ kernel.ι β = kernel.ι α ≫ f :=
by rw [φ, kernel.lift_ι]

lemma comm₄ : (ψ comm₁ comm₂) ≫ kernel.ι γ = kernel.ι β ≫ g :=
by rw [ψ, kernel.lift_ι]

lemma aux3_1 : (φ comm₁ comm₂) ≫ (ψ comm₁ comm₂) ≫ (kernel.ι γ) = (kernel.ι α) ≫ f ≫ g :=
begin
  rw [comm₄, ←category.assoc, comm₃, category.assoc],
end

lemma aux3_2 : (φ comm₁ comm₂) ≫ (ψ comm₁ comm₂) ≫ (kernel.ι γ) = 0 :=
begin
  rw [aux3_1],
  convert comp_zero,
  exact exact.w,
end

lemma aux3 : (φ comm₁ comm₂) ≫ (ψ comm₁ comm₂) = 0 :=
begin
  have aux3_3 : ((φ comm₁ comm₂) ≫ (ψ comm₁ comm₂)) ≫ (kernel.ι γ) = 0 ≫ (kernel.ι γ),
  rw [category.assoc, aux3_2, zero_comp],
  haveI : mono (kernel.ι γ) := by apply_instance,
  exact mono.right_cancellation _ _ aux3_3,
end

lemma something_in_kernel (a : A) (h : α a = 0) : ∃ (d : kernel α), kernel.ι α d = a :=
begin
  revert h,
  apply quotient.induction_on a, rintro a' ha,

  have ha2 : a'.hom ≫ α = 0 := (pseudo_zero_iff _).1 ha,
  refine ⟨⟦over.mk (kernel.lift α a'.hom ha2)⟧, _⟩,

  erw [pseudo_apply_mk, quotient.eq],
  simp only [over.mk_hom, kernel.lift_ι],
  refine ⟨a'.left, 𝟙 _, 𝟙 _, _, _, _⟩,

  apply_instance,
  apply_instance,

  simp only [over.coe_hom],
end

instance exact_φ_ψ : exact (φ comm₁ comm₂) (ψ comm₁ comm₂) :=
begin
  apply exact_of_pseudo_exact, split,
  { rintros a, rw [←comp_apply, aux3, zero_apply], },
  { intros b hb,
    have aux4_1 : ((kernel.ι β) ≫ g) b = ((ψ comm₁ comm₂) ≫ kernel.ι γ) b,
    { rw comm₄  },
    rw [comp_apply, comp_apply, hb, apply_zero] at aux4_1,
    obtain ⟨a, ha⟩ := (@pseudo_exact_of_exact V _ _ _ _ _ f g _).2 (kernel.ι β b) aux4_1,
    have aux4_2 : (α ≫ f') a = (f ≫ β) a,
    { rw comm₁ },
    erw [comp_apply, comp_apply, ha, ←comp_apply, ←comp_apply, kernel.condition,
      zero_apply, comp_apply] at aux4_2,
    have aux4_3 : f' (α a) = f' 0,
    { rw [aux4_2, apply_zero], },
    have aux4 := pseudo_injective_of_mono f' aux4_3,
    obtain ⟨a', ha'⟩ := something_in_kernel comm₁ comm₂ _ aux4,
    use a',

    have aux5_1 : ((φ comm₁ comm₂) ≫ (kernel.ι β)) a' = ((kernel.ι α) ≫ f) a',
    { rw comm₃, },
    rw [comp_apply, comp_apply, ha', ha] at aux5_1,
    haveI : mono (kernel.ι β) := by apply_instance,
    exact pseudo_injective_of_mono (kernel.ι β) aux5_1,
  }
end

end kernel_diagram

namespace cokernel_diagram

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

lemma comm₃ : f' ≫ cokernel.π β = cokernel.π α ≫ (φ' comm₁ comm₂) :=
by rw [φ', cokernel.π_desc]

lemma comm₄ : g' ≫ cokernel.π γ = cokernel.π β ≫ (ψ' comm₁ comm₂) :=
by rw [ψ', cokernel.π_desc]

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

end cokernel_diagram
