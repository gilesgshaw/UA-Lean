import logic.unique
import data.vector
import data.vector.basic
import data.vector.zip
import fin.additional

/-
The type `vector α n` is implemented as the subtype of `list α` having `length = n`.
Here we just build slightly on the theory from the library including
* 'boxing' and 'unboxing' between length-1 vectors and their values;
* conversions between vectors whose lengths are equal, but not definitionally so;
* lemmas about positive-length vectors in terms of their 'head' and 'tail'.
* 'zipping' two vectors (to make a vector of the product type)
-/

namespace vector

  -- dosen't look like this instance in in the library??
  instance unique {α : Sort*} : unique (vector α 0) :=
  {to_inhabited := {default := vector.nil}, uniq := vector.eq_nil}

  ----------------------------------------------------------------------------------
  section -- 'boxing' and 'unboxing' between length-1 vectors and their values    --
    --------------------------------------------------------------------------------
    parameter {α : Type*}
    variable {v : α}
    variable {x : vector α 1}

    def unbox: (vector α 1) → α :=
    λ x, x.nth 0

    def box: α  → (vector α 1) :=
    λ x, vector.cons x vector.nil

    @[simp] lemma box_unbox: box (unbox x) = x :=
    begin
      rw box,
      rw unbox,
      apply vector.ext,
      rw unique.forall_iff,
      simp,
    end

    @[simp] lemma box_head: box (x.head) = x :=
    begin
      rw box,
      apply vector.ext,
      rw unique.forall_iff,
      simp,
    end

    @[simp] lemma unbox_box: unbox (box v) = v := rfl

    @[simp] lemma head_box: (box v).head = v := rfl

    --------------------------------------------------------------------------------
  end     -- 'boxing' and 'unboxing' between length-1 vectors and their values    --
  ----------------------------------------------------------------------------------

  ----------------------------------------------------------------------------------
  section -- conversions between vectors whose lengths are equal                  --
    --------------------------------------------------------------------------------
    parameter {α : Type*}

    def transcribe {n m : ℕ} (equal : n = m) :
    (vector α n) → (vector α m) :=
    λ vect, ⟨ vect.val, by {simp, exact equal,} ⟩

    -- the following are all about the particular case of converting
    -- between `vector α n` and `vector α n.nat_pred.succ` for `n : N+`
    parameter {n : ℕ+}
    variable {v : vector α n}
    variable {i : fin n}
    variable {v' : vector α n.nat_pred.succ}
    variable {i' : fin n.nat_pred.succ}

    instance to_succ_pred:
    has_coe (vector α n) (vector α n.nat_pred.succ) :=
    { coe := transcribe (eq.symm (pnat.nat_pred_add_one _)) }

    instance from_succ_pred:
    has_coe (vector α n.nat_pred.succ) (vector α n) :=
    { coe := transcribe (pnat.nat_pred_add_one _) }

    lemma nth_push_succ_pred:
    (v' : vector α n).nth i = v'.nth (i : fin n.nat_pred.succ) :=
    begin -- proof is just a lot of rewriting:
      cases i,
      cases v',
      unfold_coes,
      rw transcribe,
      rw fin.transcribe,
      simp,
      rw vector.nth,
      rw vector.nth,
    end

    @[simp] lemma nth_cancel_from_succ_pred:
    (v' : vector α n).nth (i' : fin n) = v'.nth i' :=
    begin -- proof is just a lot of rewriting:
      cases i',
      cases v',
      unfold_coes,
      rw transcribe,
      rw fin.transcribe,
      simp,
      rw vector.nth,
      rw vector.nth,
    end

    @[simp] lemma nth_cancel_to_succ_pred:
    (v : vector α n.nat_pred.succ).nth (i : fin n.nat_pred.succ) = v.nth i :=
    begin -- proof is just a lot of rewriting:
      cases i,
      cases v,
      unfold_coes,
      rw transcribe,
      rw fin.transcribe,
      simp,
      rw vector.nth,
      rw vector.nth,
    end

    --------------------------------------------------------------------------------
  end     -- conversions between vectors whose lengths are equal                  --
  ----------------------------------------------------------------------------------

  ----------------------------------------------------------------------------------
  section -- positive-length vectors in terms of their 'head' and 'tail'          --
    --------------------------------------------------------------------------------
    parameter {α : Type*}
    parameter {n : ℕ}

    lemma holds_for_all_heads_and_tails (p : (vector α n.succ) → Prop) :
    (∀ v, p v) ↔ (∀ x, ∀ (w : vector α n), p (x ::ᵥ w)) :=
    begin
      split,

      -- forward direction
      intros h x w,
      specialize h (x ::ᵥ w),
      exact h,

      -- backward direction
      intros h v,
      specialize h v.head v.tail,
      simp at h,
      exact h,
    end

    lemma holds_for_head_and_tail {x y : α} {xxx yyy : vector α n}
    (φ : α → α → Prop) :
    (∀ i, φ ((x ::ᵥ xxx).nth i) ((y ::ᵥ yyy).nth i)) ↔
    (∀ j, (φ (xxx.nth j) (yyy.nth j))) ∧ φ x y :=
    begin
      split,

      -- LHS → RHS
      assume h,
      split,

      -- LHS → RHS.L
      intro j,
      specialize h j.succ,
      simp at h,
      exact h,

      -- LHS → RHS.R
      specialize h 0,
      simp at h,
      exact h,


      -- LHS → RHS
      intros h j,
      cases fin.eq_zero_or_eq_succ j with j_is_0 j_is_succesor,

      -- LHS → RHS for j=0
      rw j_is_0,
      simp,
      exact h.right,

      -- LHS → RHS for j>0
      cases j_is_succesor with k is_predecessor,
      rw is_predecessor,
      simp,
      exact h.left k,
    end

    -- alternative version in terms of a positive natural
    -- kept for posterity, though I'm not sure this is used
    -- and I think it can be achieved using what is above already
    lemma holds_for_head_and_tail_alt {m : ℕ+} {x y : α} {xxx yyy : vector α m.nat_pred}
    (φ : α → α → Prop) :
    (∀ i, φ (((x ::ᵥ xxx) : vector α m).nth i) (((y ::ᵥ yyy) : vector α m).nth i)) ↔
    (∀ j, (φ (xxx.nth j) (yyy.nth j))) ∧ φ x y :=
    begin
      split,

      -- LHS → RHS
      assume h,
      split,

      -- LHS → RHS.L
      intro j,
      specialize h j.succ,
      simp at h,
      exact h,

      -- LHS → RHS.L
      specialize h 0,
      rw nth_push_succ_pred at h,
      rw nth_push_succ_pred at h,
      simp at h,
      exact h,


      -- LHS → RHS
      intros h j,
      cases @fin.eq_zero_or_eq_succ m.nat_pred j with j_is_0 j_is_succesor,

      -- LHS → RHS for j=0
      change (j : fin (m.nat_pred.succ)) = (0 : fin m) at j_is_0,
      rw (fin.to_succ_pred_injective j_is_0),
      rw nth_push_succ_pred,
      rw nth_push_succ_pred,
      simp,
      exact h.2,

      -- LHS → RHS for j>0
      cases j_is_succesor with i is_predecesor,
      rw nth_push_succ_pred,
      rw nth_push_succ_pred,
      rw is_predecesor,
      simp,
      exact h.1 i,
    end

    --------------------------------------------------------------------------------
  end     -- positive-length vectors in terms of their 'head' and 'tail'          --
  ----------------------------------------------------------------------------------

  ----------------------------------------------------------------------------------
  section -- zip                                                                  --
    --------------------------------------------------------------------------------
    variables {α : Type*} {β : Type*} {n : ℕ} {i : fin n}
    variables {v₁ : vector α n} {v₂ : vector β n}

    -- The library contains the more general `vector.zip_with` but,
    -- unlike as with `list`, has not developed this special case:
    def zip : vector α n → vector β n → vector (α × β) n := zip_with prod.mk

    -- There are many more lemmas that could go here; I'll add them as I need them.

    @[simp] lemma map_fst_zip:
    map prod.fst (zip v₁ v₂) = v₁ :=
    begin
      apply ext,
      intro i,
      rw zip,
      simp,
    end

    @[simp] lemma map_snd_zip:
    map prod.snd (zip v₁ v₂) = v₂ :=
    begin
      apply ext,
      intro i,
      rw zip,
      simp,
    end

    @[simp] lemma nth_zip:
    (zip v₁ v₂).nth i = (v₁.nth i, v₂.nth i) :=
    begin
      rw zip,
      simp,
    end

    --------------------------------------------------------------------------------
  end     -- zip                                                                  --
  ----------------------------------------------------------------------------------
end vector
