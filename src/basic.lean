import data.set
import tactic.suggest
import tactic.basic
import data.vector
import data.vector.basic
import data.vector.zip

import vector.additional

namespace UA
  section

    --____________________________________________________________________________
    /- a signature σ is just a set (F) of operation symbols,                     /
    /  with specified (finite) arity.                                           -/

    class signature := (F : Type*) (arity_of : F → ℕ)

    parameter [σ : signature]
    include σ
    def arity_of (f) := signature.arity_of f
    variable (f : σ.F)

    /- for convinience we fix σ and the 'operations' f here.                     /
    `____________________________________________________________________________`
    /                                                                           -/


    /- A `structure` is a set (`medium`) equipped with the relevant `action`. -/

    @[class] def structure_on (medium : Type*) := -- structure on a given medium
    Π f, (vector medium (arity_of f)) → medium

    structure Structure := -- medium together with its structure
    (medium : Type*) -- should make universes explicit?
    (action : structure_on medium)

    instance Structure_to_structure_on (A : Structure) : structure_on A.medium := A.action
    instance Structure_to_sort : has_coe_to_sort Structure _ := ⟨λ str, str.medium⟩
    instance Structure_to_fun : has_coe_to_fun Structure _ := ⟨λ str, str.action⟩






  end

  section
    parameter [σ : signature]
    include σ
    variable (f : σ.F)


    /- `direct product` of two stuctures -/

    def dir_prod (A B : Structure) : Structure :=
    { medium := A.medium × B.medium,
    action := λ f input, (A.action f (vector.map prod.fst input), B.action f (vector.map prod.snd input)) }
    -- local infix `×`:55 := product



    /- A `homomorphism` is simply a function preserving the operations -/


    @[class] def preserves_σ {{α : Type*}} {{β : Type*}} [A : structure_on α] [B : structure_on β]
    (func : (α → β)) := -- predicate that a function is a homomorphism
    ∀ (f) (input : vector α (arity_of f)),
    B f (vector.map func input) = func (A f input)

    structure homomorphism (A B : Structure) := -- a function demonstrated to be a homomorphism
    (func : A → B)
    (resp_ops : preserves_σ func)

    instance homomorphism_to_fun {A B : Structure} : has_coe_to_fun (@homomorphism A B) _ := ⟨homomorphism.func⟩



    /- Simplification lemmas -/

    variables {A B : Structure}
    variable {x : vector A (arity_of f)}
    variable {y : vector B (arity_of f)}

    @[simp] lemma action_of_product : (dir_prod A B).action f =
    λ input : vector (A.medium × B.medium) (arity_of f),
    (A.action f (vector.map prod.fst input), B.action f (vector.map prod.snd input)) :=
    begin
      apply funext,
      intro x,
      rw prod.ext_iff,
      simp,

      split,
      apply congr_arg (A.action f),
      apply vector.ext,
      intro i,
      simp,

      apply congr_arg (B.action f),
      apply vector.ext,
      intro i,
      simp,
    end

    @[simp] lemma action_of_product_2 :
    (dir_prod A B).action f (vector.zip x y) = ((A.action f x), (B.action f y)) :=
    begin
      rw action_of_product,
      simp,
    end
  end


  /-` (re)define notation here globally, since we can now generalize over the parameter σ `-/
  -- infix `×`:55 := product

  -- shouldn't need these two since σ is now class-inferred
  -- postfix `-struct`:40 := @Structure
  -- infix `-struct_on `:40 := @structure_on

end UA
