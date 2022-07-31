import data.set
import tactic.suggest
import tactic.basic
import data.vector
import data.vector.basic
import data.vector.zip

import vector.additional

namespace UA
  section


    /- a signature `σ` is just a set of operation symbols, with specified (finite) arity. -/

    class signature := (F : Type*) (arity_of : F → ℕ)
    abbreviation arity_of [σ : signature] (f) := signature.arity_of f



    section
      parameter [σ : signature]
      include σ

      /- `structure_on` is a realisation of operations on a given type. -/

      @[class] def structure_on (medium : Type*) :=
      Π f, (vector medium (arity_of f)) → medium


      /- A `structure` is a `medium` equipped with the relevant `action`. -/

      structure Structure := -- medium together with its structure
      (medium : Type*) -- should make universes explicit?
      (action : structure_on medium)



      /- Coersions and instances -/

      instance Structure_to_structure_on (A : Structure) : structure_on A.medium := A.action
      instance Structure_to_sort : has_coe_to_sort Structure _ := ⟨λ str, str.medium⟩
      instance Structure_to_fun : has_coe_to_fun Structure _ := ⟨λ str, str.action⟩

    end



    parameter [σ : signature]
    include σ


    /- `direct product` of two stuctures -/

    instance dir_prod_action (α : Type*) (β : Type*) [actA : structure_on α] [actB : structure_on β] : structure_on (α × β) :=
    λ f input, (actA f (vector.map prod.fst input), actB f (vector.map prod.snd input))

    def dir_prod (A : Structure) (B : Structure) : Structure :=
    ⟨ A.medium × B.medium, dir_prod_action A.medium B.medium⟩



    /- Simplification lemmas -/

    open vector

    variables {α : Type*} [actA : structure_on α]
    variables {β : Type*} [actB : structure_on β]
    include actA actB
    variable {f : σ.F}
    variable {x : vector α (arity_of f)}
    variable {y : vector β (arity_of f)}
    variable {xy : vector (α × β) (arity_of f)}

    @[simp] lemma action_of_product:
    dir_prod_action α β f xy = (actA f (map prod.fst xy), actB f (map prod.snd xy)) :=
    begin
      rw prod.ext_iff,
      simp,

      split,
      apply congr_arg (actA f),
      apply vector.ext,
      intro i,
      simp,

      apply congr_arg (actB f),
      apply vector.ext,
      intro i,
      simp,
    end

    @[simp] lemma action_of_product_zip:
    dir_prod_action α β f (zip x y) = (actA f x, actB f y) :=
    begin
      rw action_of_product,
      simp,
    end

  end
end UA
