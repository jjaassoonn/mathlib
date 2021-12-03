import category_theory.abelian.pseudoelements
import category_theory.abelian.exact
import algebra.homology.exact
import category_theory.abelian.diagram_lemmas.pullback
import category_theory.abelian.test

noncomputable theory

open category_theory (hiding comp_apply)
open category_theory.abelian.pseudoelement
open category_theory.limits
open pullback_diagram

universes v u

variables {V : Type u} [category.{v} V] [abelian V]

local attribute [instance] preadditive.has_equalizers_of_has_kernels
local attribute [instance] object_to_sort hom_to_fun
local attribute [instance] category_theory.abelian.pseudoelement.setoid

open_locale pseudoelement zero_object

namespace connecting_map

variables {A B C A' B' C' : V}

/--
From `kernel.lean` we have:

```          φ            ψ
    kernel α --> kernel β --> kernel γ
        |           |          |
        ι (comm₃)   ι (comm₄)  ι
        |           |          |
        v           v          v
        A  ---f---> B ---g---> C -----> 0
        |           |          |
        α  (comm₁)  β  (comm₂) γ
        |           |          |
        v           v          v
0 ----> A' ---f'--> B' --g'--> C'
        |           |          |
        π  (comm₃)  π  (comm₄) π
        |           |          |
        v           v          v
  cokernel α -> cokernel β -> cokernel γ
            φ'            ψ'
```

now we define the connecting map `δ : kernel γ ⟶ cokernel α`
-/

variables {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
variables {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'}
variables [exact f g] [mono f'] [exact f' g'] [epi g]
variables (comm₁ : f ≫ β = α ≫ f') (comm₂ : g ≫ γ = β ≫ g')
include comm₁ comm₂

/- We have the following commutative diagram with exact rows
                                            ι                          snd
0 --> kernel (pullback.snd g (kernel.ι γ)) --> pullback g (kernel.ι γ) --> kernel γ
                                                          |                      |
                                                         fst      comm₃          ι
                                                          |                      |
                                                          v                      v
                            A ------------f-------------> B ---------g---------> C ----------> 0
                            |                             |                      |
                            α           comm₁             β       comm₂          γ
                            |                             |                      |
                            v                             v                      v
0 ------------------------> A' -----------f'------------> B' -------g'---------> C'
                            |                             |
                            π           comm₄            inl
                            |                             |
                            v                             v
0 ----------------------> cokernel α ----inr-----> pushout f' (cokernel.π α)

-/

-- instance : mono (kernel.ι (@pullback.fst V _ _ _ _ g (kernel.ι γ) _)) := by apply_instance
-- instance : exact (kernel.ι (@pullback.snd V _ _ _ _ g (kernel.ι γ) _))
  -- (@pullback.snd V _ _ _ _ g (kernel.ι γ) _) := exact_kernel_ι
-- instance : mono (@pushout.inr V _ _ _ _ f' (cokernel.π α) _) := by apply_instance

/- We want the following commutative diagram
B <--fst-- pullback g (kernel.ι γ) ----snd----> kernel γ
|                                                  |
β                                                  δ
|                                                  |
v                                                  v
B' --inl--> pushout f' (cokernel.π α) <--inr--- cokernel α
-/

lemma connecting_map :
  ∃ δ : kernel γ ⟶ cokernel α,
    @pullback.snd V _ _ _ _ g (kernel.ι γ) _ ≫ δ ≫ @pushout.inr V _ _ _ _ f' (cokernel.π α) _ =
    @pullback.fst V _ _ _ _ g (kernel.ι γ) _ ≫ β ≫ @pushout.inl V _ _ _ _ f' (cokernel.π α) _ :=
have aux1 : (@pullback.fst V _ _ _ _ g (kernel.ι γ) _ ≫ β) ≫ g' = 0, by
  rw [category.assoc, ←comm₂, ←category.assoc, pullback.condition, category.assoc,
    kernel.condition, comp_zero],
have aux2 : ∃ a : pullback g (kernel.ι γ) ⟶ A',
  a ≫ f' = @pullback.fst V _ _ _ _ g (kernel.ι γ) _ ≫ β, from shift_to_left _ _ aux1,
begin
  obtain ⟨a, ha⟩ := aux2,
  obtain ⟨b, hb_1, hb_2⟩ :=
    shift_upward f ((kernel.ι pullback.snd) ≫ (@pullback.fst V _ _ _ _ g (kernel.ι γ) _)),
  rw ←category.assoc at hb_2,


  /-
                                             ι                          snd
0 --> kernel (pullback.snd g (kernel.ι γ)) --> pullback g (kernel.ι γ) --> kernel γ
                            ↑                             |                      |
                            |                            fst      comm₃          ι
                            b                             |                      |
                            |                             v                      v
                            A ------------f-------------> B ---------g---------> C ----------> 0
                            |                             |                      |
                            α           comm₁             β       comm₂          γ
                            |                             |                      |
                            v                             v                      v
0 ------------------------> A' -----------f'------------> B' -------g'---------> C'
                            |                             |
                            π           comm₄            inl
                            |                             |
                            v                             v
0 ----------------------> cokernel α ----inr-----> pushout f' (cokernel.π α)

  -/

  have hb_3 : (b ≫ kernel.ι pullback.snd ≫ a) ≫ f' = α ≫ f',
  { rw [category.assoc, category.assoc, ha, ←category.assoc, ←category.assoc, hb_2, comm₁], },
  have hb_4 := mono.right_cancellation _ _ hb_3,
  have hb_5 : b ≫ kernel.ι pullback.snd ≫ a ≫ cokernel.π α = 0,
  { rw [←category.assoc, ←category.assoc, category.assoc _ _ a, hb_4, cokernel.condition], },

  resetI,
  have hb_6 := zero_of_epi_comp b hb_5,
  obtain ⟨δ, hδ⟩ := @shift_forward V _ _ (kernel pullback.snd) (pullback g (kernel.ι γ))
    (kernel γ) (cokernel α) (kernel.ι pullback.snd) pullback.snd (a ≫ cokernel.π α)
    (exact_kernel_ι) _ hb_6,

  use δ,

  erw [←category.assoc, hδ, category.assoc, ←pushout.condition, ←category.assoc, ha, category.assoc],
end

end connecting_map
