import basic

namespace UA
  section

    parameter [σ : signature]
    include σ

    /- A `homomorphism` is simply a function preserving the operations -/

    @[class] def preserves_σ {{α : Type*}} {{β : Type*}} [A : structure_on α] [B : structure_on β]
    (func : (α → β)) := -- predicate that a function is a homomorphism
    ∀ (f) (input : vector α (arity_of f)),
    B f (vector.map func input) = func (A f input)

    structure homomorphism (A B : Structure) := -- a function demonstrated to be a homomorphism
    (func : A → B)
    (resp_ops : preserves_σ func)

    instance homomorphism_to_fun {A B : Structure} : has_coe_to_fun (@homomorphism A B) _ := ⟨homomorphism.func⟩

  end
end UA
