import basic

namespace UA
  universes u_lang u_str

  section

    parameter [σ : signature.{u_lang}]
    include σ

    /- a `subStructure` is a subset which is closed under the operations -/

    variable {α : Type u_str}
    variable [act : structure_on α]

    @[class] def closed (sub_medium : set α) :=
    ∀ (f) (input : vector α _), set.range input.nth ⊆ sub_medium → act f input ∈ sub_medium

    def subStructure (A : Structure.{u_lang u_str}) : Type u_str :=
    subtype (@closed A.medium A.action)

  end
end UA
