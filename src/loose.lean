import logic.nonempty
import data.vector.basic

/-
Lemmas that are either just used when a proof is in development,
or I suspect are in the library but haven't found yet.
-/

lemma ap_fun {α : Type*} {β : Type*} {f : α → β} {x : α} :
(λ a, f a) x = f x := rfl

lemma specialize_by_fun {α : Type*} {β : Type*} (f : α → β) {p : β → Prop} :
(∀ y, p y) → (∀ x, p (f x)) := λ h x, h (f x)

noncomputable def partial_section {α : Type*} {β : Type*} (f : α → β) : (set.range f) → α := λ y,
@classical.choice {x // f x = y} (nonempty_subtype.mpr (by {cases y.property with x _, use x, assumption}))

theorem partial_section_prop {α : Type*} {β : Type*} {f : α → β} {y : β} (h : y ∈ set.range f) :
f (partial_section f ⟨y, h⟩) = y := (@classical.choice {x // f x = y} _).prop

theorem partial_section_prop_2 {α : Type*} {β : Type*} {f : α → β} :
f ∘ partial_section f = subtype.val := funext (λ y, partial_section_prop y.prop)

noncomputable def section_of_quot {α : Type*} (r : α → α → Prop) (q : quot r) : α :=
@classical.choice {a // quot.mk r a = q} (nonempty_subtype.mpr (quot.exists_rep q))

theorem section_of_quot_section {α : Type*} {r : α → α → Prop} :
quot.mk r ∘ section_of_quot r = id :=
funext (λ q, (classical.choice (nonempty_subtype.mpr (quot.exists_rep q))).property)

lemma vector.map_comp_2 {α : Type*} {β : Type*} {γ : Type*} {n : ℕ} {f : α → β} {g : β → γ} {v : vector α n} :
vector.map (g ∘ f) v = vector.map g (vector.map f v) :=
begin
  apply vector.ext,
  simp,
end

lemma vector.map_comp {α : Type*} {β : Type*} {γ : Type*} {n : ℕ} {f : α → β} {g : β → γ} :
@vector.map _ _ n (g ∘ f) = (vector.map g) ∘ (vector.map f) := funext (λ v, vector.map_comp_2)
