import basic
import loose

namespace UA
  universes u_lang u_strA u_strB

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
end UA
