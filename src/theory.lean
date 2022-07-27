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
      split, all_goals {intro h_main}, {

        apply set.Union₂_subset,

        intros ax is_ax,
        specialize @h_main ax is_ax,       -- introduce spesific axiom and specialize

        rw [st_instances, set.Union_subset_iff],

        intros subst eqn equal,            -- `subst` witnesses the valididity of `eqn`
        apply h_main eqn,                  -- so the hypothesis says that `eqn` holds
        rw [st_instances, set.mem_Union],
        exact exists.intro subst equal,    -- after we provide the witness `subst`

      },
      {

        intros ax is_ax inst is_inst,      -- have 2 variables with 2 properties

        apply h_main inst,
        rw [ax_instances, set.mem_Union],
        apply exists.intro ax,
        rw set.mem_Union,                  -- specialize to variables

        exact exists.intro is_ax is_inst,  -- use properties

      },
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
