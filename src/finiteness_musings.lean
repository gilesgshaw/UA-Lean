import foundations
import logic.equiv.fin
import logic.equiv.set
import data.set.basic
import data.fin.basic
import data.finite.basic
import trivial

-- This construction is convinient for my treatment of finite sets,
-- though the cardinality `c` would be provably 'unique' (in the set theoretic sense) anyway.
-- Admitedly having the witness bears no moral advantage, since we still have to invoke LEM
-- to reason about the contents of the set anyway.
-- In contrast, the `finitetype` and `finiteset` constructions keep track of this data,
-- in a genuinely constructive way.
structure demonstably_finite (α : Type*) := (c : ℕ) (eqv : (fin c) ≃ α)

noncomputable def classify_subsingleton (α : Type) (H : subsingleton α) :
plift (α ≃ (fin 0)) ⊕ plift (α ≃ (fin 1)) :=
begin

  cases LEM (is_empty α) with h hh,
  cases LEM (nonempty α) with hhh hhhh,
  apply sum.inr,
  apply plift.up,
  apply equiv.symm,
  apply equiv.trans fin_one_equiv,
  apply equiv.symm,
  apply definite_description_3 H,
  exact plift.down hhh,

  apply sum.inl,
  apply plift.up,
  apply equiv.symm,
  apply equiv.trans fin_zero_equiv,
  apply equiv.symm,
  apply @equiv.equiv_empty _ _,
  apply plift.down,
  assumption,

  cases LEM (nonempty α) with hhh hhhh,
  apply sum.inr,
  apply plift.up,
  apply equiv.symm,
  apply equiv.trans fin_one_equiv,
  apply equiv.symm,
  apply definite_description_3 H,
  apply plift.down,
  assumption,

  apply sum.inl,
  apply plift.up,
  apply equiv.symm,
  apply equiv.trans fin_zero_equiv,
  apply equiv.symm,
  apply @equiv.equiv_empty _ _,
  apply not_nonempty_iff.1,
  exact plift.down hhhh,

end

-- this is basically in the library, but is convinient to have on hand
def equiv.set.subset {α : Type*} {X Y : set α} (H : Y ⊆ X) :
{x : α // x ∈ Y} ≃ {x : X // x.val ∈ Y} := {
to_fun    := λ a, ⟨⟨a, H a.property⟩, a.property⟩,
inv_fun   := λ b, ⟨b, b.property⟩,
left_inv  := λ x, by {apply subtype.ext, refl},
right_inv := λ x, by {apply subtype.ext, simp}}

universe u -- to stop the elaborator generating spurious universe variables for the next theorem


/- *** This theorem is one of the leftovers. ***
-- I wrote it to replace `equiv.set.union'`, while avoiding any non-constructive axioms.
-- In truth the only reason `equiv.set.union'` uses choice I believe is because
-- it has snuck in the the very defenition of `set.has_union` - since this is part of the boolean
-- algebra of subsets, of which LEM is needed to assert certain axioms.
-- In the end I needed something slightly different, for which I just copied said proof instead.
-- In any case I wrote this before I realised that my approach to finite sets would need LEM
-- anyway so it has become doubly redundant!                                                   -/
def sum_eqv {α : Type u} (p q : α → Prop) (dj : ∀ x, p x → q x → false) [decidable_pred p] :
{a // p a} ⊕ {a // q a} ≃ {a // p a ∨ q a} :=
begin
  apply equiv.symm,

  calc {a // p a ∨ q a} ≃ {x : {a // p a ∨ q a} // p x} ⊕ {x : {a // p a ∨ q a} // ¬p x} : _
  ...                   ≃ {x : {a // p a ∨ q a} // p x} ⊕ {x : {a // p a ∨ q a} // q x} : _
  ...                   ≃ {x // p x} ⊕ {x // q x} : _,

  apply equiv.symm,
  exact equiv.sum_compl (λ x : {a // p a ∨ q a}, p x),

  apply equiv.sum_congr,
  exact equiv.refl _,
  apply equiv.set_congr,
  apply set.ext,
  intro a,
  split,
  cases a.property,
  intro b,
  exact absurd h b,
  intro b,
  exact h,
  cases a.property,
  intro b,
  exact absurd b (dj a h),
  intros b c,
  exact dj a c b,

  apply equiv.symm,
  apply equiv.sum_congr,
  apply equiv.set.subset,
  intros x h,
  left,
  assumption,
  apply equiv.set.subset,
  intros x h,
  right,
  assumption,

end


protected def lem_truncate_to_fun {n : ℕ} (P : (fin n.succ) → Prop) (H : ¬ P 0) :
{x : fin n.succ // P x} → {x : fin n // P x.succ} :=
λ xp, ⟨⟨xp.val.val.pred,
begin
  rw ← nat.succ_lt_succ_iff,
  convert xp.val.property,
  apply sps,
  by_contra,
  apply different xp.property H,
  apply subtype.ext,
  assumption,
end⟩,
begin
  convert xp.property,
  apply subtype.ext,
  rw fin.succ,
  simp,
  apply sps,
  by_contra,
  apply different xp.property H,
  apply subtype.ext,
  assumption,
end⟩

protected def lem_truncate_inv_fun {n : ℕ} (P : (fin n.succ) → Prop) (H : ¬ P 0) :
{x : fin n // P x.succ} → {x : fin n.succ // P x} := λ x, ⟨x.val.succ, x.property⟩

protected def lem_truncate {n : ℕ} (P : (fin n.succ) → Prop) (H : ¬ P 0) :
{x : fin n.succ // P x} ≃ {x : fin n // P x.succ} := {
to_fun := lem_truncate_to_fun P H,
inv_fun := lem_truncate_inv_fun P H,
left_inv := begin
  intro x,
  apply subtype.ext,
  apply subtype.ext,
  rw lem_truncate_inv_fun,
  rw lem_truncate_to_fun,
  simp,
  apply sps,
  by_contra,
  apply different x.property H,
  apply subtype.ext,
  assumption,
end,
right_inv := begin
  intro x,
  apply subtype.ext,
  apply subtype.ext,
  rw lem_truncate_inv_fun,
  rw lem_truncate_to_fun,
  simp,
end}



/- Copied straight from `equiv.set.union'`,
-- though rephrased so as to avoid unnessesary axioms. -/
protected def equiv.set.union'_alt {α} {s t : set α}
(p : α → Prop) [decidable_pred p]
(hs : ∀ x ∈ s, p x)
(ht : ∀ x ∈ t, ¬ p x) : {x : α // x ∈ s ∨ x ∈ t} ≃ s ⊕ t :=
{ to_fun := λ x, if hp : p x
then sum.inl ⟨_, x.2.resolve_right (λ xt, ht _ xt hp)⟩
else sum.inr ⟨_, x.2.resolve_left (λ xs, hp (hs _ xs))⟩,
inv_fun := λ o, match o with
| (sum.inl x) := ⟨x, or.inl x.2⟩
| (sum.inr x) := ⟨x, or.inr x.2⟩
end,
left_inv := λ ⟨x, h'⟩, by by_cases p x; simp [equiv.set.union'_alt._match_1, h]; congr,
right_inv := λ o, begin
  rcases o with ⟨x, h⟩ | ⟨x, h⟩;
  dsimp [equiv.set.union'_alt._match_1];
  [simp [hs _ h], simp [ht _ h]]
end }

def n_plus_0 {n : ℕ} : fin n ≃ (fin n ⊕ fin 0) :=
{ to_fun := sum.inl,
inv_fun := λ x, begin
  cases x,
  exact x,
  exact absurd x.property (nat.not_lt_zero _),
end,
left_inv := λ x, by {simp},
right_inv := λ x, begin
  cases x,
  simp,
  exact absurd x.property (nat.not_lt_zero _),
end}

lemma eq_of_le_of_not_lt' {a b : ℕ} (hab : a ≤ b) (hba : ¬ a < b) : a = b :=
begin
  apply nat.eq_of_lt_succ_of_not_lt,
  apply nat.lt_succ_iff.2,
  assumption,
  assumption,
end

noncomputable def eq_last_or_eq_cast_succ' {n : ℕ} (i : fin (n+1)) :
plift (i = fin.last n) ⊕ plift {j : fin n // i = j.cast_succ} :=
begin
  cases LEM (i.val < n),
  right,
  apply plift.up,
  have hyp : i = fin.cast_succ ⟨↑i, plift.down val⟩,
  rw fin.cast_succ_mk,
  exact subtype.ext rfl,
  exact ⟨⟨i, plift.down val⟩, hyp⟩,
  left,
  apply plift.up,
  apply subtype.ext,
  exact eq_of_le_of_not_lt' (nat.lt_succ_iff.mp i.property) (plift.down val),
end



noncomputable def last_cases {n : ℕ} {C : Sort*}
(hlast : C) (hcast : (fin n) → C) (i : fin (n + 1)) : C :=
dite_artificial (i.val < n) (λ t, hcast ⟨i.val, t⟩) (λ _, hlast)

lemma last_cases_last {n : ℕ} {C : Sort*}
(hlast : C) (hcast : (fin n) → C) :
(last_cases hlast hcast (fin.last n): C) = hlast :=
begin
  rw last_cases,
  apply dite_artificial_false,
  simp,
end

lemma last_cases_cast_succ {n : ℕ} {C : Sort*}
(hlast : C) (hcast : (fin n) → C) (i : fin n) :
(last_cases hlast hcast (fin.cast_succ i): C ) = hcast i :=
begin
  rw last_cases,
  simp,
  apply dite_artificial_true,
  exact i.property,
end



noncomputable def n_plus_1 {n : ℕ} : fin n.succ ≃ (fin n ⊕ fin 1) :=
{ to_fun := @last_cases _ (fin n ⊕ fin 1) (sum.inr 0) (λ x, (sum.inl x)),
inv_fun := λ x, begin
  cases x,
  exact fin.cast_succ x,
  exact fin.last n,
end,
left_inv := λ x, begin
  cases eq_last_or_eq_cast_succ' x,
  rw plift.down val,
  rw last_cases_last,
  rw (plift.down val).property,
  rw last_cases_cast_succ,
end,
right_inv := λ x, begin
  cases x,
  rw last_cases_cast_succ,
  rw last_cases_last,
  simp,
end}

noncomputable def augment_set {n : ℕ} {α β : Type} :
demonstably_finite α → subsingleton β → demonstably_finite (α ⊕ β) :=
begin
  intros df ss,
  cases classify_subsingleton β ss,

  apply demonstably_finite.mk df.c,
  apply equiv.symm,
  calc α ⊕ β ≃ fin df.c ⊕ fin 0: _
  ...         ≃ fin df.c : _,

  apply equiv.sum_congr,
  apply equiv.symm,
  exact df.eqv,
  exact plift.down val,
  apply equiv.symm,
  exact n_plus_0,

  apply demonstably_finite.mk df.c.succ,
  apply equiv.symm,
  calc α ⊕ β ≃ fin df.c ⊕ fin 1: _
  ...         ≃ fin df.c.succ : _,

  apply equiv.sum_congr,
  apply equiv.symm,
  exact df.eqv,
  exact plift.down val,
  apply equiv.symm,
  exact n_plus_1,

end

protected noncomputable def lem_subset_finite {n : ℕ} (S : set (fin n)) : demonstably_finite S :=
begin
  induction n with n h_ind,
  use 0,
  apply equiv.equiv_of_is_empty,

  have ss : subsingleton {a // S a ∧ a = 0},
  apply subsingleton.intro,
  intros x y,
  apply subtype.ext,
  unfold_coes,
  rw x.property.right,
  rw y.property.right,



  have rrr : {a // S a} ≃ {x : (fin n) // S x.succ ∧ x.succ ≠ 0} ⊕ {a // S a ∧ a = 0},
  calc {a // S a} ≃ {a // (S a ∧ a ≠ 0) ∨ (S a ∧ a = 0)}   : _
  ...             ≃ {a // S a ∧ a ≠ 0} ⊕ {a // S a ∧ a = 0} : _
  ...             ≃ {x : (fin n) // S x.succ ∧ x.succ ≠ 0} ⊕ {a // S a ∧ a = 0} : _,


  apply equiv.set_congr,
  apply set.ext,
  intro x,
  split,
  intro h,
  cases nat.decidable_eq x 0,
  left,
  split,
  assumption,
  intro contra,
  apply h_1,
  apply (@subtype.ext_iff ℕ _ x (0 : (fin n.succ))).1,
  assumption,
  right,
  split,
  assumption,
  apply subtype.ext,
  assumption,
  intro h,
  cases h,
  exact h.left,
  exact h.left,

  apply @equiv.set.union'_alt (fin n.succ) {a | S a ∧ a ≠ 0} {a | S a ∧ a = 0} (λ x, x ≠ 0) _,
  intros x h,
  exact h.right,
  intros x h1 h2,
  exact h2 h1.right,

  apply equiv.sum_congr,
  exact lem_truncate {a | S a ∧ a ≠ 0} (λ h, h.right rfl),
  apply equiv.refl,


  have ssssss := @augment_set n _ _ (h_ind
  {x : (fin n) | {a | S a ∧ a ≠ 0} x.succ}) ss,
  apply demonstably_finite.mk ssssss.c,
  exact equiv.trans ssssss.eqv (equiv.symm rrr),
end

theorem set_finite {α : Type} {S : set α} : finite α → finite S :=
begin
  intro I,
  unfreezingI {
  cases I with N eqv_N,
  cases lem_subset_finite (eqv_N '' S) with n eqv_n,
  use n,
  apply equiv.symm,
  apply equiv.trans eqv_n,
  apply equiv.symm,
  exact eqv_N.image S, },
end

theorem subset_finite {α : Type} {S T : set α} (H : T ⊆ S) : finite S → finite T :=
λ s_fin, @finite.of_equiv _ _ (@set_finite _ _ s_fin) (equiv.set.subset H).symm
