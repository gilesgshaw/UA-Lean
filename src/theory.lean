import data.set
import data.set.basic
import tactic.suggest
import tactic.basic
import tactic.nth_rewrite.default

import loose
import cong

namespace UA
  universes u_lang u_str u_t

  section


    /- A theory `τ`, over σ, is a set of `axioms` which must hold universally. -/

    class theory extends signature.{u_lang} :=
    (axioms_ : set (word.{u_lang} ℕ × word.{u_lang} ℕ))

    abbreviation equation [σ : signature.{u_lang}] (T : Type u_t) := word T × word T
    local notation `sentance` := equation ℕ

    /- Formally an `equation` is just a pair of words. A `sentance` is an equation in
    -- which the variables are intended to be arbitrary (i.e. placeholders).       -/


    section
      parameter [τ : theory.{u_lang}]
      include τ


      -- all instances of a sentance within a given set
      def st_instances (T : Type u_t) (st : sentance) : set (equation T) :=
      ⋃ subst : ℕ → T, {(subst† st.fst, subst† st.snd)}

      -- all instances of our axioms within a given set
      def ax_instances (T : Type u_t) : set (equation T) :=
      (⋃ ax ∈ τ.axioms_, st_instances T ax)

      -- the interpretation of an equation in a given structure
      def eval_eqn {α : Type u_str} [act : action_on α] (e : equation α) : α × α :=
      (eval e.fst, eval e.snd)

      -- those sentances which are 'modelled' by a given structure
      def true_sentances (α : Type u_str) [act : action_on α] : set sentance :=
      λ st, ∀ inst ∈ st_instances α st, (eval_eqn inst).fst = (eval_eqn inst).snd

      -- predicate that a structure satisfies the axioms of τ
      @[class] def satisfies_τ (α : Type u_str) [act : action_on α] := τ.axioms_ ⊆ true_sentances α

      -- more user-friendly version of this statement
      lemma satisfies_iff (α : Type u_str) [act : action_on α] : satisfies_τ α ↔
      ∀ inst ∈ ax_instances α, (eval_eqn inst).fst = (eval_eqn inst).snd :=
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
    end

    section
      parameter [τ : theory.{u_lang}]
      include τ

      /- Given any structure, we can enfore the axioms in the 'free-est' possible way.
      -- The construction of 'free objects' (e.g. groups) is a special case of this -/

      def enforce_axioms : Π X : Structure.{u_lang u_str}, congruence X :=
      λ X, UA.congruence.gen_by_set (eval_eqn '' (ax_instances X))

      -- proof a bit long, might try and silm down later
      theorem axioms_enforced {X : Structure.{u_lang u_str}} : satisfies_τ (enforce_axioms X).quotient :=
      begin

        let C := enforce_axioms X, -- the congruence on X
        let X' := C.quotient,      -- the quotient object

        apply (satisfies_iff X').2,
        intros eqn eqn_is_axiom,

        cases eqn with lhs rhs,
        simp_rw [ax_instances, set.mem_Union] at eqn_is_axiom,
        cases eqn_is_axiom with ax eqn_is_axiom,
        cases eqn_is_axiom with is_axiom eqn_is_axiom,
        simp_rw [st_instances, set.mem_Union] at eqn_is_axiom,
        cases eqn_is_axiom with substitution eqn_is_axiom,
        simp_rw [set.mem_singleton_iff, prod.ext_iff] at eqn_is_axiom,
        cases eqn_is_axiom with left_is_axiom right_is_axiom,
        simp_rw [left_is_axiom, right_is_axiom, eval_eqn],

        let lift_of_subst := section_of_quot C.r ∘ substitution,
        have lift_compatable : C.π ∘ lift_of_subst = substitution, {
          rw ← function.comp.assoc,
          simp_rw [congruence.π, section_of_quot_section],
          exact function.comp.left_id _,
        },

        rw ← lift_compatable,
        nth_rewrite_lhs 0 translation_functorial,
        nth_rewrite_rhs 0 translation_functorial,

        simp_rw ← hom_iff.1 C.proj_is_hom (lift_of_subst† ax.fst),
        simp_rw ← hom_iff.1 C.proj_is_hom (lift_of_subst† ax.snd),

        apply quot.sound,
        apply congruence.gentd_contains_gens,
        rw set.mem_image,
        use ((translate (section_of_quot C.r) lhs),
        (translate (section_of_quot C.r) rhs)),
        split,

        -- witness is valid
        rw ax_instances,
        rw set.mem_Union,
        use ax,
        rw set.mem_Union,
        use is_axiom,
        rw st_instances,
        rw set.mem_Union,
        use lift_of_subst,
        rw set.mem_singleton_iff,
        apply prod.ext; {
          simp,
          nth_rewrite_rhs 0 translation_functorial,
          apply congr_arg,
          assumption,
        },

        -- witness is correct
        nth_rewrite_rhs 0 translation_functorial,
        nth_rewrite_rhs 1 translation_functorial,
        rw eval_eqn,
        apply prod.ext; {
          simp,
          apply congr_arg,
          apply congr_arg,
          assumption,
        },

      end

    end

    parameter [τ : theory.{u_lang}]
    include τ


    /- A τ-`Object` is just a structure satisfying the axioms of τ. -/

    structure Object :=
    (medium      : Type u_str)
    (action      : action_on.{u_lang u_str} medium)
    (satf_axioms : satisfies_τ medium)


  end
end UA
