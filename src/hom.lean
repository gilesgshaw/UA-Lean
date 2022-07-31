import basic

namespace UA
  section

    parameter [σ : signature]
    include σ

    /- A `homomorphism` is simply a function preserving the operations -/

    @[class] def preserves_σ
    {{α : Type*}} {{β : Type*}} [actA : structure_on α] [actB : structure_on β]
    (func : (α → β)) : Prop := ∀ f v, actB f (vector.map func v) = func (actA f v)

    def Homomorphism
    (α : Type*) (β : Type*) [actA : structure_on α] [actB : structure_on β] :=
    subtype (@preserves_σ α β actA actB)


  end
end UA
