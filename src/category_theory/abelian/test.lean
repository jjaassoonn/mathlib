import category_theory.abelian.exact

noncomputable theory

open category_theory
open category_theory.limits

universes v u

variables {V : Type u} [category.{v} V] [abelian V]

open_locale zero_object

section

variables {A B C D : V}

/--
                D
                |
                h
                |
                v
0 ---> A --f--> B --g--> C
-/

variables (f : A ⟶ B) (g : B ⟶ C) {h : D ⟶ B} [exact f g] [mono f]
variables (eq_zero : h ≫ g = 0)

lemma is_kernel : is_limit (kernel_fork.of_ι f (show f ≫ g = 0, by simp)) :=
begin
  haveI : is_iso ((abelian.is_limit_image f g).lift
    (kernel_fork.of_ι f (show f ≫ g = 0, by simp))),
  { convert category_theory.abelian.images.is_iso_factor_thru_image f using 1 },
  exact (abelian.is_limit_image f g).of_point_iso
end

include g eq_zero

lemma shift_to_left : ∃ h' : D ⟶ A, h' ≫ f = h :=
begin
  have := kernel_fork.is_limit.lift' (is_kernel f g) h eq_zero,
  exact ⟨this.1, this.2⟩,
end

end

section

variables {A B C X : V}

/--
           X
           |
           h
           |
           v
A ---f---> B ---g---> C --> 0
-/

variables (f : A ⟶ B) (g : B ⟶ C) (h : X ⟶ B) [mono h] [X ≅ kernel g] [exact f g] [epi g]

lemma aux1 : image.ι f ≫ g = 0 :=
begin
  refine zero_of_epi_comp (factor_thru_image f) _,
  rw [←category.assoc, image.fac, exact.w],
end

lemma shift_upward : ∃ (x : A ⟶ X), epi x ∧ x ≫ h = f := sorry

end

section

variables {A B C D : V}

/--

0 ---> A --f--> B --g--> C
                |
                h
                |
                v
                D

--/

variables (f : A ⟶ B) (g : B ⟶ C) {h : B ⟶ D} [exact f g] [mono f]
variable (eq_zero : f ≫ h = 0)

include eq_zero
lemma shift_forward : ∃ (h' : C ⟶ D), g ≫ h' = h := sorry


end
