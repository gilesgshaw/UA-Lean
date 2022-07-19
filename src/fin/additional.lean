import data.nat.basic
import data.pnat.basic
import data.fin.basic

/-
The type `fin n` gives a finite ordinal of size `n : N` (whose elements are `0 ... n-1`).
This file is just some additional housekeeping to build on the existing library.
In particular we develop the theory of `fin ↑m` where `m : N+` is a positive natural.
-/

namespace fin

  -- express a finite ordinal in two (equal) ways
  def transcribe {a b : ℕ} (equal : a = b) : (fin a) → (fin b) :=
  λ i, ⟨ i.val, by {have l := i.property, rw ← equal, exact l,} ⟩

  -- the standard library has `fin.has_zero (fin (succ n))` for `n : N`.
  -- we include a similar entry here, directly for `fin m` with `m : N+`.
  instance of_pnat_has_zero {m : ℕ+} :
  has_zero (fin (m : nat)) := ⟨⟨0, m.property⟩⟩

  @[simp] lemma to_nat_zero {m : ℕ+} :
  ((0 : fin m) : ℕ) = 0 := rfl

  ----------------------------------------------------------------------------------
  section -- conversions between `fin m` and `fin m.nat_pred.succ` for `m : N+`   --
    --------------------------------------------------------------------------------
    variable {m : ℕ+}

    instance to_succ_pred :
    has_coe (fin m) (fin m.nat_pred.succ) :=
    {coe := transcribe (eq.symm (pnat.nat_pred_add_one _)) }

    instance from_succ_pred :
    has_coe (fin m.nat_pred.succ) (fin m) :=
    {coe := transcribe (pnat.nat_pred_add_one _) }

    @[simp] lemma from_succ_pred_to_succ_pred :
    ∀ i : fin m.nat_pred.succ, ((i : fin m) : fin m.nat_pred.succ) = i :=
    begin
      intro i,
      unfold_coes,
      rw transcribe,
      rw transcribe,
      simp,
    end

    @[simp] lemma to_succ_pred_from_succ_pred :
    ∀ i : fin m, ((i : fin m.nat_pred.succ) : fin m) = i :=
    begin
      intro i,
      unfold_coes,
      rw transcribe,
      rw transcribe,
      simp,
    end

    lemma for_all_to_succ_pred {p : fin m.nat_pred.succ → Prop} :
    (∀ i : fin m, p i) → (∀ i, p i) :=
    begin
      intros h i,
      specialize h i,
      simp at h,
      exact h,
    end

    lemma for_all_from_succ_pred {p : fin m → Prop} :
    (∀ i : fin m.nat_pred.succ, p i) → (∀ i, p i) :=
    begin
      intros h i,
      specialize h i,
      simp at h,
      exact h,
    end

    lemma from_succ_pred_injective {i j : fin m.nat_pred.succ} :
    (i : fin m) = (j : fin m) → i = j :=
    begin
      intro h,
      have lem : ((i : fin m) : fin m.nat_pred.succ) = ((j : fin m) : fin m.nat_pred.succ),
      apply congr_arg,
      exact h,
      simp at lem,
      exact lem,
    end

    lemma to_succ_pred_injective {i j : fin m} :
    (i : fin m.nat_pred.succ) = (j : fin m.nat_pred.succ) → i = j :=
    begin
      intro h,
      have lem : ((i : fin m.nat_pred.succ) : fin m) = ((j : fin m.nat_pred.succ) : fin m),
      apply congr_arg,
      exact h,
      simp at lem,
      exact lem,
    end

    @[simp] lemma from_succ_pred_zero :
    ((0 : fin m.nat_pred.succ) : fin m) = 0
    := subtype.ext rfl

    @[simp] lemma to_succ_pred_zero :
    ((0 : fin m) : fin m.nat_pred.succ) = 0
    := subtype.ext rfl

    --------------------------------------------------------------------------------
  end     -- conversions between `fin m` and `fin m.nat_pred.succ` for `m : N+`   --
  ----------------------------------------------------------------------------------

end fin
