import basic
import loose

import category_theory.concrete_category.unbundled_hom

open category_theory

namespace UA
  universes u_lang u_str u_strA u_strB u_strC

  section

    /- We wrap the main defenitions in sections,
    -- so that they become universe polymorphic within this file -/

    section
      parameter [σ : signature.{u_lang}]
      include σ

      /- A `homomorphism` is simply a function preserving the operations -/

      @[class] def homomorphism
      {{α : Type u_strA}} {{β : Type u_strB}} [actA : structure_on α] [actB : structure_on β]
      (func : (α → β)) : Prop := ∀ f v, actB f (vector.map func v) = func (actA f v)

      def Homomorphism
      (α : Type u_strA) (β : Type u_strB) [actA : structure_on α] [actB : structure_on β] :
      Type (max u_strA u_strB) := subtype (@homomorphism α β actA actB)

    end

    section
      parameter [σ : signature.{u_lang}]
      include σ

      -- variables must be in this order for the category theory methods

      variables {α : Type u_strA} {β : Type u_strB} {γ : Type u_strC}
      variables [A : structure_on α] [B : structure_on β] [C : structure_on γ]

      include A
      instance id_is_hom : homomorphism (@id α) :=
      λ _ _, by { rw [vector.map_id], refl }

      include B C
      instance comp_is_hom {g : β → γ} {f : α → β}
      [h_g : homomorphism g] [h_f : homomorphism f] : homomorphism (g ∘ f) :=
      λ _ _, by { rw [function.comp_app, ← h_f, vector.map_comp, ← h_g] }

    end

    section
      parameter [σ : signature.{u_lang}]
      include σ

      /- `homomorphism_` and `Homomorphism_` are varients where we require a consistent
      -- universe level in the underlying sets, being at least `u_lang`.
      -- This is needed by much of the category theory infastructure in mathlib       -/

      abbreviation homomorphism_
      {{α β : Type (max u_lang u_str)}} [actA : structure_on α] [actB : structure_on β]
      (func : (α → β)) : Prop :=
      @homomorphism.{u_lang (max u_lang u_str) (max u_lang u_str)} _ α β actA actB func

      abbreviation Homomorphism_
      (α β : Type (max u_lang u_str)) [actA : structure_on α] [actB : structure_on β] :
      Type (max u_lang u_str) :=
      @Homomorphism.{u_lang (max u_lang u_str) (max u_lang u_str)} _ α β actA actB

    end

    parameter [σ : signature.{u_lang}]
    include σ



    /- `unbundled_hom` is the data of a concrete category, that is, where morphisms
    -- are a subtype of maps between the underlying types of the objects.
    -- This is exactly the information we have defined in our current treatment.  -/

    instance str_unbundled_hom : unbundled_hom homomorphism_.{u_lang u_str} := {
      hom_id := @UA.id_is_hom _,
      hom_comp := @UA.comp_is_hom _,
    }

    /- `bundled_hom` is the data of a category in general, where morphisms can be
    -- a type in their own right. We generate this automatically from the above. -/

    instance str_bundled_hom : bundled_hom Homomorphism_.{u_lang u_str} :=
    unbundled_hom.bundled_hom structure_on_ homomorphism_

    /- Now we let `STRUCTURE` refer to the category of σ-Structures. -/

    instance STRUCTURE : large_category.{max u_lang u_str} Structure_ :=
    bundled_hom.category Homomorphism


  end
end UA
