--import trivial
import logic.equiv.basic
import data.set.basic

/-
lemma finite_implies_bounded_2 (S : set ℕ) :
finite S → ∃ N, ∀ n ∈ S, n ≤ N :=
begin
  intro h,
  cases h with n h_card,
  revert S,
  induction n with n h_ind,

  intros S h_card,
  use 0,
  cases h_card with func _ _ _,
  intros n h_n,
  have contra := (func ⟨n, h_n⟩),
  exact fin_zero_elim contra,

  intros S h,

  let red := (@reduce_at_zero _ _ S _ h),
  let outlier := h.inv_fun 0,

  specialize h_ind (S \ {outlier}) red,
  cases h_ind with N h_N,

  use outlier ⊔ N,

  intros x in_s,
  set x' : S := ⟨x, in_s⟩,
  rw le_sup_iff,

  cases fin.eq_zero_or_eq_succ (h.to_fun x'),

  left,
  have temp := (congr_arg h.inv_fun h_1),
  rw h.left_inv x' at temp,
  have ss : x = ↑x', by {refl}, rw ss,
  have s : (x' : ℕ) = (outlier : ℕ) := congr_arg _ temp, rw s,

  right,
  cases h_1 with index h_index,
  apply h_N x,
  split,
  exact in_s,
  rw set.mem_singleton_iff,
  intro h_contra,
  have temp : x' = outlier,
  exact subtype.ext h_contra,
  rw temp at h_index,
  rw h.right_inv 0 at h_index,
  exact (fin.succ_ne_zero index) (eq.symm h_index),
end
-/

/-
lemma bounded_implies_finite (S : set ℕ) :
∃ N, ∀ n ∈ S, n ≤ N → finite S :=
begin

end
-/


-- unfold_full
-- reducible
-- Type* vs Sort* ??

/-
lemma pow_1_is_self (x y) : (r^1) x y ↔ r (unbox x) (unbox y) :=
begin
  rw pow,
  simp,
  rw unique.forall_iff,
  rw unbox,
  simp,
end
-/

/-
lemma pow_is_eqv {N : ℕ} : equivalence r → equivalence (r^N) :=
begin
  intro r_is_eqv,

  split,
  intros xxx i,
  exact r_is_eqv.left (xxx.nth i),

  split,
  intros _ _ h_xy i,
  exact r_is_eqv.right.left (h_xy i),

  intros _ _ _ h_xy h_yz i,
  exact r_is_eqv.right.right (h_xy i) (h_yz i),
end
-/


-- function.swap (or something) is more general than this
-- but using this one makes the elaborator more happy sometimes
-- def sw {α : Type*} {β : Type*} {γ : Type*}
-- (f : α → β → γ) : β → α → γ := λ y x, f x y
--@[simp] lemma sw_simp {α : Type*} {β : Type*} {γ : Type*}
--{f : α → β → γ} {a : α} {b : β}: (sw f) b a = f a b := rfl



--IMPORTANT:
-- forall_swap
-- exists_comm
-- set.range_subset_iff
-- set.mem_def

/-
theorem compute
{α : Type*} {β : Type*} {r : α → α → Prop} (f : α → β)
( h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂ )
:
∀ a : α, quot.lift  f h (quot.mk r a) = f a := λ a, rfl
-/

--simp_rw set.mem_def at h,

-- the ith projection operation
-- def π {I : Type u} {α : Type v} (i) : ((I → α) → α) := λ t, t i

--def subobject (x y : Structure) :=
--(x.medium : set y.medium)


--def is_subobject {α : Type*} {β : set α} (A : object_on α) (B : object_on β) :=
--∀ f b, ↑(B f b) = A f ↑b

--def is_homomorphism {A : object} {B : object} (h : A → B) :=
--∀ f a, h (A f a) = B f (h ∘ a)

--universes u v
-- variable {α : Type 0}
-- variable {β : Type v}
-- #check @image α β
-- variable (S : Structure)
-- variable (input : (fin (σ.arity_of f)) → S.medium)
-- #check @image (fin (σ.arity_of f)) S.medium input

-- def image {α : Type 0} {β : Type k} (f : α → β) := set.image f (λ _, tt)
-- has_coe_to_sort (fin (arity_of f) → (product A A).medium) (tuple_pair (arity_of f) ↥A)
-- instance xxx {N : ℕ} {α : Type*} : has_coe (tuple N (α × α)) (tuple_pair N α)
-- := ⟨λ x, ⟨λ i, (x i).fst, λ i, (x i).snd⟩⟩




-- noncomputable theory
-- open_locale classical



def type_inc {α : Type*} {X : set α} {Y : set α} (H : X ⊆ Y) : X → Y := λ x, ⟨x, H x.property⟩
def isolate_fn {α : Type*} {β : Type*} (f : α → β) : α → set.range f := λ x, ⟨f x, set.mem_range_self x⟩


noncomputable def choice_alt {α : Type*} {p : α → Prop} : (∃ a : α, p a) → α :=
λ H, classical.choice (@nonempty_of_exists α p H)

def rel_is_eqv {α : Type*} {β : Type*} (r : α → β → Prop) := (∀ a, ∃! b, r a b) ∧ (∀ b, ∃! a, r a b)

def rel_of_fun {α : Type*} {β : Type*} (f : α → β) : α → β → Prop := λ x y, f x = y
noncomputable def fun_of_eqv {α : Type*} {β : Type*} {r : α → β → Prop}
(H : rel_is_eqv r) : α → β := λ a, choice_alt (H.1 a)

theorem rel_of_equiv {α : Type*} {β : Type*} {φ : α ≃ β} : rel_is_eqv (rel_of_fun φ.to_fun) :=
begin
  split,

  intro a,
  use φ.to_fun a,
  split,

  rw rel_of_fun,

  intro _,
  exact eq.symm,

  intro b,
  use φ.inv_fun b,
  split,

  rw rel_of_fun,
  rw φ.right_inv b,

  intros s _,
  rw ← φ.left_inv s,
  apply congr_arg φ.inv_fun,
  assumption,
end
