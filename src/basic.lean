import data.set
import tactic.suggest
import tactic.basic
import data.vector
import data.vector.basic
import data.vector.zip

import vector.additional

namespace UA
  universes u_lang u_str u_strA u_strB

  section


    /- a signature `σ` is just a set of operation symbols, with specified (finite) arity. -/

    class signature := (F : Type u_lang) (arity_of : F → ℕ)
    abbreviation arity_of [σ : signature] (f) := signature.arity_of f


    /- The universes `u_strX` of the structures may be distinct, and different to `u_lang`.
    -- We wrap the main defenitions in a section,
    -- so that they become universe polymorphic within this file. -/

    section
      parameter [σ : signature.{u_lang}]
      include σ

      /- `structure_on` is a realisation of operations on a given type. -/

      @[class] def structure_on (medium : Type u_str) : Type (max u_lang u_str) :=
      Π f, (vector medium (arity_of f)) → medium


      /- A `structure` is a `medium` equipped with the relevant `action`. -/

      structure Structure : Type (max u_lang (u_str+1)) :=
      (medium : Type u_str)
      (action : structure_on medium)



      /- Coersions and instances -/

      instance Structure_to_structure_on (A : Structure) : structure_on A.medium := A.action
      instance Structure_to_sort : has_coe_to_sort Structure _ := ⟨λ str, str.medium⟩
      instance Structure_to_fun : has_coe_to_fun Structure _ := ⟨λ str, str.action⟩

    end



    parameter [σ : signature.{u_lang}]
    include σ


    /- `direct product` of two stuctures -/

    instance dir_prod_action (α : Type u_strA) (β : Type u_strB)
    [actA : structure_on α] [actB : structure_on β] : structure_on (α × β) :=
    λ f input, (actA f (vector.map prod.fst input), actB f (vector.map prod.snd input))

    def dir_prod (A : Structure) (B : Structure) : Structure :=
    ⟨ A.medium × B.medium, dir_prod_action A.medium B.medium⟩



    /- Simplification lemmas -/

    open vector

    variables {α : Type u_strA} [actA : structure_on α]
    variables {β : Type u_strB} [actB : structure_on β]
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
