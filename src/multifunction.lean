import vector.additional

/-
This file defines currying and uncurrying for multivariate functions
-/

namespace multi
  section

    parameter {α : Type*}
    parameter {β : Type*}
    parameter {γ : Type*}
    parameter {n : ℕ}

    definition curry_by_head:
    ((vector α n.succ) → β) → α → (vector α n) → β :=
    λ f x yyy, f (x ::ᵥ yyy)

    @[simp] lemma curry_by_head_simp
    {f : (vector α n.succ) → β} {a : α} {v : vector α n}:
    curry_by_head f a v = f (a ::ᵥ v) := rfl

    definition curry_by_tail:
    ((vector α n.succ) → β) → (vector α n) → α → β :=
    λ f yyy x, f (x ::ᵥ yyy)

    @[simp] lemma curry_by_tail_simp
    {f : (vector α n.succ) → β} {v : vector α n} {a : α}:
    curry_by_tail f v a = f (a ::ᵥ v) := rfl

    definition uncurry_by_head:
    (α → (vector α n) → β) → (vector α n.succ) → β :=
    λ f xxx, f xxx.head xxx.tail

    definition uncurry_by_tail:
    ((vector α n) → α → β) → (vector α n.succ) → β :=
    λ f xxx, f xxx.tail xxx.head


    parameter {m : ℕ+}

    definition curry_by_head_alt:
    ((vector α m) → β) → α → (vector α m.nat_pred) → β :=
    λ f x yyy, f (x ::ᵥ yyy)

    definition curry_by_tail_alt:
    ((vector α m) → β) → (vector α m.nat_pred) → α → β :=
    λ f yyy x, f (x ::ᵥ yyy)

    definition uncurry_by_head_alt:
    (α → (vector α m.nat_pred) → β) → (vector α m) → β :=
    λ f xxx, f (xxx : vector α m.nat_pred.succ).head xxx.tail

    definition uncurry_by_tail_alt:
    ((vector α m.nat_pred) → α → β) → (vector α m) → β :=
    λ f xxx, f xxx.tail (xxx : vector α m.nat_pred.succ).head

  end
end multi
