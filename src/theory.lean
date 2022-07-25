import data.set
import data.set.basic
import tactic.suggest
import tactic.basic

import words

namespace UA
  section

    --____________________________________________________________________________
    /- A theory `τ`, over σ, is a set of `axioms` which must hold universally.   /
    /  That is, they are simply universally quantified equations.
    /  (We do not allow conditional equations, or horn clauses.)                -/

    structure theory extends signature :=
    (axioms_ : set (to_signature-word ℕ × to_signature-word ℕ))

    parameter {τ : theory}

    def σ := τ.to_signature
    def equation (T : Type*) := σ-word T × σ-word T
    local notation `sentance` := equation ℕ

    /- For convinience, we understand by `equation` simply a pair of words.
    -- A `sentance` is an equation in which the variables are intended to be
    -- arbitrary (i.e. placeholders). We use the naturals for this purpouse.     /
    `____________________________________________________________________________`
    /                                                                           -/


    -- all instances of a sentance within a given set
    def st_instances (T : Type*) (st : sentance) : set (equation T) :=
    ⋃ subst : ℕ → T, {(subst* st.fst, subst* st.snd)}

    -- all instances of our axioms within a given set
    def ax_instances (T : Type*) : set (equation T) :=
    (⋃ ax ∈ τ.axioms_, st_instances T ax)

    -- the interpretation of an equation in a given structure
    def eval_eqn {T : Type*} [act : σ-struct_on T] (e : equation T) : T × T :=
    (eval e.fst, eval e.snd)

    -- those sentances which are 'modelled' by a given structure
    def true_sentances (T : Type*) [act : σ-struct_on T] : set sentance :=
    λ st, ∀ inst ∈ st_instances T st, (eval_eqn inst).fst = (eval_eqn inst).snd

    -- predicate that a structure satisfies the axioms of τ
    def satisfies_τ (T : Type*) [act : σ-struct_on T] := τ.axioms_ ⊆ true_sentances T

    -- more user-friendly version of this statement
    lemma satisfies_iff (T : Type*) [act : σ-struct_on T] : satisfies_τ T ↔
    ∀ inst ∈ ax_instances T, (eval_eqn inst).fst = (eval_eqn inst).snd :=
    begin
      split,
      intros h eqn is_inst,
      rw satisfies_τ at h,
      rw ax_instances at is_inst,
      revert eqn,

      let ss := {eqn : equation T | (eval_eqn eqn).fst = (eval_eqn eqn).snd},
      change ((⋃ (ax ∈ τ.axioms_), st_instances T ax) ⊆ ss),
      apply set.Union₂_subset,

      intros ax is_ax,
      specialize @h ax is_ax,
      rw true_sentances at h,
      rw set.mem_def at h,
      rw st_instances,
      apply set.Union_subset,
      intro subst,
      intros eqn is_given,
      specialize h eqn,
      simp_rw set.mem_singleton_iff at is_given,
      rw is_given,
      have h := h _,
      have hhh : eqn ∈ ss,
      exact h,
      rw ← is_given,
      exact hhh,
      rw st_instances,
      rw set.mem_Union,
      use subst,
      simp,
      exact is_given,


      intro h,
      rw satisfies_τ,
      intros ax is_ax,
      rw true_sentances,
      intros inst is_inst,
      specialize h inst,
      apply h,
      rw ax_instances,
      rw set.mem_Union,
      use ax,
      rw set.mem_Union,
      use is_ax,
      assumption,
    end



    /- A τ-`Object` is just a structure satisfying the axioms of τ. -/

    structure Object :=
    (medium      : Type*)
    (action      : σ-struct_on medium)
    (satf_axioms : satisfies_τ medium)


    /- Given any structure, we can enfore the axioms in the 'free-est' possible way.
    -- The construction of 'free objects' (e.g. groups) is a special case of this -/

    def enforce_axioms : Π X : σ-struct, congruence X :=
    λ X, UA.congruence.gen_by_set (eval_eqn '' (ax_instances X))

  end
end UA
