import words

namespace UA
  universes u_lang u_str u_strA u_strB

  section

    /- We wrap the main defenitions in a section,
    -- so that they become universe polymorphic within this file. -/

    section
      parameter [σ : signature.{u_lang}]
      include σ

      /- a `subStructure` is a subset which is closed under the operations -/

      variable {α : Type u_str}
      variable [act : action_on α]

      @[class] def closed (sub_medium : set α) :=
      ∀ (f) (input : vector α _), set.range input.nth ⊆ sub_medium → act f input ∈ sub_medium

      def subStructure (A : Structure.{u_lang u_str}) : Type u_str :=
      subtype (@closed A.medium A.action)

    end

    parameter [σ : signature.{u_lang}]
    include σ



    instance image_is_closed
    {{α : Type u_strA}} {{β : Type u_strB}} [actA : action_on α] [actB : action_on β]
    (φ : (α → β)) [hom : homomorphism φ] : closed (set.range φ) :=
    begin
      intros f yyy h,
      rw set.range_subset_iff at h,
      use actA f (vector.of_fn (λ i, partial_section φ ⟨yyy.nth i, h i⟩)),
      rw ← hom _ _,
      apply congr_arg,
      apply vector.ext,
      intro i,
      rw [vector.nth_map, vector.nth_of_fn, @partial_section_prop _ _ φ _ _],
    end

    lemma eval_on_substructure
    {{α : Type u_str}} [actA : action_on α] (X : set α) [cls : closed X] (w : word α) :
    vars w ⊆ X → eval w ∈ X := λ h,
    begin
      induction w with _ f www h_ind, {
        exact h (set.mem_singleton _),
      },
      {
        apply cls f (vector.of_fn (eval ∘ www)),
        rw set.range_subset_iff,
        intro i,
        rw vector.nth_of_fn,
        rw [vars, set.Union_subset_iff] at h,
        exact h_ind i (h i),
      },
    end

    lemma closed_iff
    {α : Type u_str} [actA : action_on α] {X : set α} :
    closed X ↔ ∀ w : word α, vars w ⊆ X → eval w ∈ X :=
    begin
      split, {
        introI,
        exact eval_on_substructure X,
      },
      {
        intros h_main f xxx h,
        convert h_main (word.opr f (word.var ∘ xxx.nth)) _, {
          apply vector.ext,
          intro i,
          rw vector.nth_of_fn,
          refl,
        },
        {
          simp_rw [vars, set.Union_subset_iff, set.singleton_subset_iff],
          rw [set.range_subset_iff] at h,
          exact h,
        },
      },
    end

    def closure {{α : Type u_str}} [actA : action_on α] (X : set α) : set α :=
    ⋂₀ { S | closed S ∧ X ⊆ S}

    instance closure_is_closed {α : Type u_str} [actA : action_on α] {X : set α} :
    closed (closure X) :=
    begin
      intros _ _ h_x S h_S,
      apply h_S.left _ _,
      revert h_x S,
      rw [closure, ← set.le_eq_subset, ← set.Inf_eq_sInter],
      exact le_Inf_iff.1,
    end

    lemma closure_inflationary {α : Type u_str} [actA : action_on α] {X : set α} :
    X ⊆ closure X :=
    begin
      intros _ _ S h_S,
      apply h_S.right _,
      assumption,
    end

    lemma closure_eq {α : Type u_str} [actA : action_on α] {X : set α} :
    closure X = eval '' {w | vars w ⊆ X} :=
    begin
      apply set.subset.antisymm,
      {
        rw [closure, ← set.le_eq_subset, ← set.Inf_eq_sInter],
        apply Inf_le _,
        rw set.le_eq_subset,
        split,
        {
          intros f xxx h,
          simp_rw [set.range_subset_iff, set.mem_image] at h,
          cases choose_from_relation _ h with www h_w,
          rw set.mem_image,
          use word.opr f www,
          split,
          {
            rw [set.mem_set_of_eq, vars, set.Union_subset_iff],
            exact λ i, (h_w i).left,
          },
          {
            convert eq.symm (UA.eval_is_hom _ (vector.of_fn www)),
            exact funext (λ i, (eq.symm (vector.nth_of_fn _ i))),
            apply vector.ext,
            intro i,
            rw [vector.nth_map, vector.nth_of_fn],
            exact eq.symm (h_w i).right,
          },
        },
        {
          intros x h_x,
          rw set.mem_image_eq,
          use word.var x,
          rw [set.mem_set_of_eq, vars],
          exact ⟨set.singleton_subset_iff.mpr h_x, rfl⟩,
        },
      },
      {
        rw set.image_subset_iff,
        intro w,
        rw set.mem_preimage,
        induction w with w f www h_ind; intro h,
        {
          rw [set.mem_set_of_eq, vars, set.singleton_subset_iff] at h,
          exact closure_inflationary h,
        },
        {
          refine UA.closure_is_closed f (vector.of_fn (eval ∘ www)) _,
          rw set.range_subset_iff,
          intro i,
          rw vector.nth_of_fn,
          rw [set.mem_set_of_eq, vars, set.Union_subset_iff] at h,
          exact (h_ind i) (h i),
        },
      },
    end


  end
end UA
