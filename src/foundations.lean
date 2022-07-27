import logic.equiv.basic

variable {α : Sort*}
variable {p : α → Prop}



/- *** The axiom of 'definite description' ***

-- An axiom which would seems uncontroversial to a set theorist, but in our
-- current foundations it jepourdises constructivity in a very real sense.
-- (As we are reminded when having to mark everything 'noncomputable')   -/

axiom definite_description : (∃! x : α, true) → α

noncomputable def definite_description_1 : (∃! x, p x) → {x // p x}
:= λ h, definite_description
begin
  cases h with x h',
  use x,
  exact h'.left,
  exact ⟨trivial, λ a _, subtype.ext (h'.right a a.property)⟩,
end

noncomputable def definite_description_2: subsingleton α → nonempty α → α :=
assume h_subsg h_nE,
begin
  apply definite_description,
  apply @exists.elim α (λ x, true),
  apply exists_true_iff_nonempty.2,
  assumption,
  intros a h,
  use a,
  exact ⟨trivial, λ b _, @subsingleton.elim _ h_subsg b a⟩,
end

noncomputable def definite_description_3: subsingleton α → nonempty α → α ≃ unit :=
assume h_subsg h_nE, {
to_fun := λ x, unit.star,
inv_fun := λ s, definite_description_2 h_subsg h_nE,
left_inv := λ x, @subsingleton.elim _ h_subsg _ _,
right_inv := λ s, unit.ext}



/- *** The law of excluded middle ***

-- A strong version of the law of excluded middle,
-- which is tantermount to allowing the 'construction' of objects
-- based on cases of `p` being true or false -/
axiom LEM (p : Prop) : plift p ⊕ plift ¬ p

-- using `plift` and `⊕` has just the same effect as the inbuilt `decidable` class
noncomputable def decidability (p : Prop) : decidable p :=
begin
  cases LEM p,
  apply decidable.is_true,
  exact plift.down val,
  apply decidable.is_false,
  exact plift.down val,
end

-- this statement is weaker, since the `∨` type is one which, by design,
-- can only be used to 'motivate' propositions, rather than general types
theorem LEM_weak (p : Prop) : p ∨ ¬ p :=
begin
  cases LEM p,
  left,
  exact plift.down val,
  right,
  exact plift.down val,
end



/- *** 'If(_, if_true, if_false)' function ***

-- A version of `dite` from the core library, which automally calls upon the
-- axiomised instance of `decidable`.
-- The true and false cases in `dite` must be functions of the witnesses in order that
-- the recursor for the `decidable` structure is actually able to pass the value of
-- this structure to each of the branches. Moreover we retain this behaviour here,
-- since the witnesses are often used themselves in the construction of the output -/

noncomputable def dite_artificial (c : Prop) (t : c → α) (f : ¬ c → α) : α :=
@dite α c (decidability c) t f

@[simp] lemma dite_artificial_true {c : Prop} (t : c → α) (f : ¬ c → α) (w : c) :
dite_artificial _ t f = t w := @dif_pos c (decidability c) w α t f

@[simp] lemma dite_artificial_false {c : Prop} (t : c → α) (f : ¬ c → α) (w : ¬ c) :
dite_artificial _ t f = f w := @dif_neg c (decidability c) w α t f
