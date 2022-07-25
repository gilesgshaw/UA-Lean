
/-
Give an alternative characterisation `eqv_gen_alt` of `eqv_gen`, the equiverlance relation generated
by a binary relation, and prove it is the same.

Also define the infix `contains` which will refer to binary relations.
-/

namespace relation

  def contains_ {α : Type*} (r : α → α → Prop) (s : α → α → Prop) := ∀ x y : α, s x y → r x y
  infix ` contains `:55 := contains_

  section
    parameter {α : Type*}
    variable (r : α → α → Prop)
    variables (x y : α)

    def eqv_gen_alt (r) (x y) := ∀ (s : α → α → Prop), equivalence s → s contains r → s x y

    theorem eqv_gen_alt_is_reflexive : reflexive (eqv_gen_alt r) :=
    begin
      intros x s h_eqv h_contains,
      exact h_eqv.left x,
    end

    theorem eqv_gen_alt_is_symmetric : symmetric (eqv_gen_alt r) :=
    begin
      intros x y h s h_eqv h_contains,
      specialize h s h_eqv h_contains,
      exact h_eqv.right.left h,
    end

    theorem eqv_gen_alt_is_transitive : transitive (eqv_gen_alt r) :=
    begin
      intros x y z h_xy h_yz s h_eqv h_contains,
      specialize h_xy s h_eqv h_contains,
      specialize h_yz s h_eqv h_contains,
      exact h_eqv.right.right h_xy h_yz,
    end

    theorem eqv_gen_alt_is_equivalence : equivalence (eqv_gen_alt r) :=
    begin
      rw equivalence,
      split,
      exact eqv_gen_alt_is_reflexive r,
      split,
      exact eqv_gen_alt_is_symmetric r,
      exact eqv_gen_alt_is_transitive r,
    end

    theorem eqv_gen_alt_same : (eqv_gen r) x y ↔ (eqv_gen_alt r) x y :=
    begin
      split,

      intro h,
      induction h,
      case eqv_gen.rel   : a b               { intros _ _ h_contains, specialize h_contains a b, cc, },
      case eqv_gen.refl  : a                 { exact  eqv_gen_alt_is_reflexive r a, },
      case eqv_gen.symm  : a b   _   hab     { exact  eqv_gen_alt_is_symmetric r hab, },
      case eqv_gen.trans : a b c _ _ hab hbc { exact eqv_gen_alt_is_transitive r hab hbc, },

      intro h,
      exact h (eqv_gen r) (eqv_gen.is_equivalence r) (eqv_gen.rel),
    end

  end
end relation
