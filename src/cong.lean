import sub
import hom
import multiquotient
import relation.additional

namespace UA
  universes u_lang u_str

  section

    parameter [σ : signature.{u_lang}]
    include σ


    /- A `congruence` is an equiverlance relation which is 'respected' by the operations. This is
    -- precisely the condition required for the quotient set to be a well-defined structure.   -/

    section
      parameter {α : Type u_str}
      parameter [act : structure_on α]


      -- the operations are said to 'respect' a binary relation ~ if,
      -- in an equation f (x, y, z) = a,
      -- altering an input x → x' where x ~ x'
      -- causes a similar alteration on the output
      def operations_respect_relation (r : α → α → Prop) :=
      ∀ (f : σ.F) (xxx yyy : vector α (arity_of f)),
      (∀ i, r (xxx.nth i) (yyy.nth i)) → r (act f xxx) (act f yyy)

      -- a binary relation on the structure A is respected by the operations
      -- if and only if it is closed as a subset of the product structure
      lemma relation_is_closed_iff_respected {r} :
      operations_respect_relation r ↔ closed (λ (p : α×α), r p.1 p.2) :=
      begin
        split,

        intros h f xyxyxy h_input,
        specialize h f (vector.map prod.fst xyxyxy) (vector.map prod.snd xyxyxy),
        rw set.range_subset_iff at h_input,
        simp at h,
        exact h h_input,

        intros h f xxx yyy h_input,
        specialize h f (vector.zip xxx yyy),
        rw set.range_subset_iff at h,
        simp at h,
        exact h h_input,
      end



      /- *** congruence generated by a binary relation *** -/

      inductive cong_gen (r : α → α → Prop) : α → α → Prop
      | rel   {} (  x y) : r x y → cong_gen x y
      | refl  {} (    x) : cong_gen x x
      | symm  {} (  x y) : cong_gen x y → cong_gen y x
      | trans {} (x y z) : cong_gen x y → cong_gen y z → cong_gen x z
      | op    {}     (f) (xxx : vector α _) (yyy : vector α _)
      : (∀ i, cong_gen (xxx.nth i) (yyy.nth i)) → cong_gen (act f xxx) (act f yyy)

      theorem cong_gen_is_equivalence {r} : equivalence (cong_gen r) :=
      mk_equivalence _ cong_gen.refl cong_gen.symm cong_gen.trans

      theorem cong_gen_is_respected {r} : operations_respect_relation (cong_gen r) :=
      begin
        rw relation_is_closed_iff_respected,
        intros f input h,
        rw set.subset_def at h,
        rw set.forall_range_iff at h,
        have lem := cong_gen.op f (vector.map prod.fst input) (vector.map prod.snd input),
        simp at lem,
        exact lem h,
      end



      /- *** alternative characterisation of congruence generated  ***-/

      def smallest_cong_ctg (r) (x y) :=
      ∀ s, operations_respect_relation s → equivalence s → s contains r → s x y

      lemma smallest_cong_ctg_is_respected {r} : operations_respect_relation (smallest_cong_ctg r) :=
      begin
        intros f xxx yyy h,
        intros s s_closed s_eqv s_contains,
        apply s_closed f xxx yyy,
        intro i,
        exact h i s s_closed s_eqv s_contains,
      end

      theorem smallest_cong_ctg_is_equivalence {r} : equivalence (smallest_cong_ctg r) :=
      begin
        rw equivalence,
        split,
        intros x s h_closed h_eqv h_contains,
        exact h_eqv.left x,

        split,
        intros x y h s h_closed h_eqv h_contains,
        specialize h s h_closed h_eqv h_contains,
        exact h_eqv.right.left h,

        intros x y z h_xy h_yz s h_closed h_eqv h_contains,
        specialize h_xy s h_closed h_eqv h_contains,
        specialize h_yz s h_closed h_eqv h_contains,
        exact h_eqv.right.right h_xy h_yz,
      end

      theorem cong_gen_is_smallest_containing {r x y} : (cong_gen r) x y ↔ (smallest_cong_ctg r) x y :=
      begin

        split,
        intro h,
        induction h,

        case cong_gen.rel   : a b               { intros _ _ _ h_contains, specialize h_contains a b, cc, },
        case cong_gen.refl  : a                 { exact (smallest_cong_ctg_is_equivalence).left a, },
        case cong_gen.symm  : a b   _   hab     { exact (smallest_cong_ctg_is_equivalence).right.left hab, },
        case cong_gen.trans : a b c _ _ hab hbc { exact (smallest_cong_ctg_is_equivalence).right.right hab hbc, },

        case cong_gen.op : f xxx yyy h i_hyp  {
          have r_respects_spefific_input :
          ((∀ i, smallest_cong_ctg r (xxx.nth i) (yyy.nth i)) → smallest_cong_ctg r (act f xxx) (act f yyy)),
          intro i, exact smallest_cong_ctg_is_respected f xxx yyy i,
          exact r_respects_spefific_input i_hyp,
        },

        intro h,
        exact h (cong_gen r) (cong_gen_is_respected) (cong_gen_is_equivalence) (cong_gen.rel),

      end
    end


    /- We implement `congruence` as a class (in the vein of setoid). -/

    class congruence (α : Type u_str) [act : structure_on α] :=
    (s : setoid α) (closed : operations_respect_relation s.r)

    instance congruence_setoid {α : Type u_str} [act : structure_on α]
    [cong : congruence α] : setoid α := cong.s

    namespace congruence
      section
        parameter {α : Type u_str}
        parameter [act : structure_on α]
        parameter (self : congruence α)

        def r := self.s.r
        def π := quot.mk r

        theorem respectful {f} {{a b : vector α _}} :
        (∀ i, a.nth i ≈ b.nth i) → π (act f a) = π (act f b) :=
        begin
          intro h,
          apply quot.sound,
          apply congruence.closed,
          exact h,
        end

        instance quotient_action : structure_on (quot r) :=
        λ f, mquotient.lift (π ∘ act f) (respectful)

        instance proj_is_hom : @homomorphism _ _ _ act _ π := λ _ _, by { apply mquotient.comp }

        def quotient : Structure.{u_lang u_str} := ⟨quot r, quotient_action⟩
        def proj : Homomorphism α quotient := ⟨π, proj_is_hom⟩


        @[simp] lemma action_of_quotient {{f}} {{p}} :
        quotient_action f p = (mquotient.lift (π ∘ act f) (respectful)) p := rfl


        include act
        def gen_by (r : α → α → Prop) : congruence α := ⟨setoid.mk (cong_gen r) (cong_gen_is_equivalence), cong_gen_is_respected⟩
        def gen_by_set (R : set (α × α)) : congruence α := gen_by (λ x y, (x, y) ∈ R)
        lemma gentd_contains_gens {R} {x y} : (x, y) ∈ R → (gen_by_set R).r x y := λ h, cong_gen.rel _ _ h
        omit act

      end
    end congruence

  end
end UA
