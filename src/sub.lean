import basic

namespace UA
  section

    parameter [σ : signature]
    include σ

    /- a `subStructure` is a subset which is closed under the operations -/

    variable {α : Type*}
    variable [act : structure_on α]

    @[class] def closed (sub_medium : set α) :=
    ∀ (f) (input : vector α (arity_of f)), set.range input.nth ⊆ sub_medium → act f input ∈ sub_medium

    def subStructure (A : Structure) : Type* :=
    subtype (@closed A.medium A.action)

  end
end UA
