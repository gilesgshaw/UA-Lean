import data.set.basic
import data.set

theorem different {α : Type} {p : α → Prop} {x y : α} :
p x → ¬ p y → x ≠ y :=
begin
  intros h1 h2 h3,
  rw h3 at h1,
  exact h2 h1,
end

theorem sps {n : ℕ} : n ≠ 0 → n.pred.succ = n :=
begin
  intro h,
  cases n,
  exact absurd rfl h,
  rw nat.pred,
end

lemma union_subset_iff_alt {α : Type*} {β : Type*} {f : α → β} {X : set α} {Y : set β} :
(⋃ x ∈ X, {f x}) ⊆ Y ↔ (∀ x ∈ X, f x ∈ Y)
:=
begin
  split,

  intros h x in_X,
  apply @h (f x),
  rw set.mem_Union,
  use x,
  rw set.mem_Union,
  use in_X,
  refine set.mem_singleton _,

  intros h x in_U,
  rw set.mem_Union at in_U,
  cases in_U with a in_U,
  rw set.mem_Union at in_U,
  cases in_U with h_a h_x,
  convert h a h_a,
end

lemma union_subset_1 {α : Type*} {β : Type*} {f : α → set β} {X : set α} {Y : set β} :
(⋃ x ∈ X, f x) ⊆ Y → (∀ x ∈ X, f x ⊆ Y)
:=
begin
  intros h x in_X y y_in_fx,
  apply @h y,
  rw set.mem_Union,
  use x,
  rw set.mem_Union,
  use in_X,
  assumption,
end

-- exact set.Union₂_subset,
lemma union_subset_2 {α : Type*} {β : Type*} {f : α → set β} {X : set α} {Y : set β} :
(∀ x ∈ X, f x ⊆ Y) → (⋃ x ∈ X, f x) ⊆ Y
:=
begin
  intros h y in_U,
  cases in_U with Y' h_Y',
  cases h_Y' with h_Y' h_y,
  rw set.range at h_Y',
  simp at h_Y',
  cases h_Y' with x h_Y',
  specialize h x,
  rw ← h_Y' at h_y,
  rw set.mem_Union at h_y,
  cases h_y with h_x h_y,
  apply @h h_x y,
  assumption,
end

-- exact set.Union_subset,
lemma range_subset_2 {α : Type*} {β : Type*} {f : α → set β} {Y : set β} :
(∀ x, f x ⊆ Y) → (⋃ x, f x) ⊆ Y
:=
begin
  intros h y in_U,
  cases in_U with Y' h_Y',
  cases h_Y' with h_Y' h_y,
  rw set.range at h_Y',
  simp at h_Y',
  cases h_Y' with x h_Y',
  specialize h x,
  rw ← h_Y' at h_y,
  apply @h y,
  assumption,
end

lemma fin_last_or_not {n : ℕ} (i : fin n.succ) :
(i = fin.last n) ∨ (∃ j : fin n, i = j.cast_succ) :=
begin
  cases lt_or_le (i : ℕ) (n : ℕ),

  right,
  use i,
  assumption,
  apply subtype.ext,
  rw fin.cast_succ_mk,
  refl,

  left,
  apply subtype.ext,
  apply nat.eq_of_le_of_lt_succ,
  assumption,
  exact i.property,
end

def finite_choice {α : Type*} {n : ℕ} (r : fin n → α → Prop) :
(∀ i, ∃ a, r i a) → (∃ f : _ → α, ∀ i, r i (f i)) :=
begin
  induction n with n h_ind,

  intro h,
  use default,
  intro i,
  exact absurd i.property (nat.not_lt_zero _),

  intro h,
  specialize h_ind (r ∘ fin.cast_succ),
  cases h_ind (λ i : fin n, h (fin.cast_succ i)) with f_prev h_f,
  specialize h (fin.last n),
  cases h with a h_a,

  use @fin.last_cases _ (λ _, α) a f_prev,
  intro i,
  cases fin_last_or_not i with i_eq_n i_lt_n,
  rw i_eq_n,
  rw fin.last_cases_last,
  assumption,

  cases i_lt_n with i' i_eq_i',
  specialize h_f i',
  simp at h_f,
  rw i_eq_i',
  rw fin.last_cases_cast_succ,
  assumption,
end

def finite_choice_reps {α : Type*} {n : ℕ} {r : α → α → Prop} :
∀ f : fin n → quot r, ∃ f', quot.mk r ∘ f' = f :=
begin
  intro f,
  have choices := finite_choice (λ i q, quot.mk r q = f i) _,
  cases choices with f' h_f',
  use f',
  exact funext h_f',

  intro i,
  apply quot.exists_rep,
end

lemma vector_map_of_of_fn {α : Type*} {β : Type*} {n} (f : fin n → α) (g : α → β) :
vector.map g (vector.of_fn f) = vector.of_fn (g ∘ f) :=
begin
  apply vector.ext,
  intro m,
  simp,
end

def choose_from_relation {α : Type*} {β : Type*} (r : α → β → Prop) :
(∀ i, ∃ a, r i a) → (∃ f : α → β, ∀ i, r i (f i)) :=
begin
  intro h,

  let dependant_choice_function : Π a, {b : β // r a b} :=
  λ a, classical.choice (nonempty_subtype.mpr (h a)),

  use λ a, (dependant_choice_function a),
  exact λ a, (dependant_choice_function a).property,
end

def choice_reps {α : Type*} {r : α → α → Prop} :
∀ f : α → quot r, ∃ f', quot.mk r ∘ f' = f :=
begin
  intro f,

  let quot_rel := λ i q, quot.mk r q = f i,
  cases choose_from_relation quot_rel _ with f' h_f',
  use f',
  exact funext h_f',

  intro i,
  apply quot.exists_rep,
end
