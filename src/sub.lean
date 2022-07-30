import basic

namespace UA
  section

    parameter [σ : signature]
    include σ

    /- a `subStructure` is a subset which is closed under the operations -/

    def closed_under {medium : Type*} (sub_medium : set medium) (action : structure_on medium) :=
    ∀ (f) (input : vector medium (arity_of f)), set.range input.nth ⊆ sub_medium → action f input ∈ sub_medium
    local infix ` is_closed_under `:55 := closed_under

    def closed {medium : Type*} [action : structure_on medium] (sub_medium : set medium) :=
    sub_medium is_closed_under action
    local postfix ` is_closed `:55 := closed

    structure subStructure (A : Structure) := -- a subset demonstrated to be closed
    (sub_medium : set A)
    (closed : sub_medium is_closed)

  end

  infix ` is_closed_under `:55 := closed_under
  postfix ` is_closed `:55 := closed -- check this isn't useless...

end UA
