import multifunction
open vector

/-
We recreate the familiar theory about lifting maps through quotients,
but for multivariate functions (i.e. functions `(vector α n) → β`). Namely,
we introduce counterparts to the `mk`, `ind`, `lift` and `sound` declerations
in `quot` and `quotient`, as well as the relevant 'computation principles'.
-/

namespace multi

  def rel (α : Type*) := α → α → Prop

  section
    -- fix a particular relation:
    parameter {α : Type*}
    parameter {r : rel α}
    parameter (ref : reflexive r)
    -- we imagine this to be an equiverlance relation,
    -- though in fact our proofs only ever require it to be reflexive

    variable {β : Type*}
    variable {n : ℕ}

    -- `f` is `respectful` if it respects `r` in each variable
    def rrr : rel (vector α n) := λ a b, ∀ i, r (a.nth i) (b.nth i)
    def respectful (f : (vector α n) → β) := (∀ a b, rrr a b → f a = f b)
    local postfix ` is_respectful`:55 := respectful

    -- `multivar_map` keeps track of such a function
    structure multivar_map {n : ℕ} {β : Type*} :=
    (f : (vector α n) → β)
    (resp : f is_respectful)
    local infix `-var_map_to `:55 := @multivar_map


    include ref
    -- if all variables respect r, in particular the first does
    theorem head_is_respectful (map : n+1-var_map_to β) {{a b}} :
    r a b → (curry_by_head map.f) a = (curry_by_head map.f) b :=
    begin

      intro hab,
      apply funext,
      intro _,

      rw curry_by_head,
      simp,

      apply map.resp _ _,
      apply (holds_for_head_and_tail r).2,
      split,
      exact λ _, ref _,
      exact hab,

    end
    omit ref

    -- quotient by the first variable alone
    def quotient_off_head:
    (n+1-var_map_to β) → (vector α n → quot r → β) := λ map,
    function.swap (quot.lift (curry_by_head map.f) (head_is_respectful map))

    -- the result of quotienting by the first variable
    -- respects r in all of the remaining variables
    include ref
    lemma quotient_is_respectful (map : n+1-var_map_to β) :
    (quotient_off_head map) is_respectful :=
    begin

      intros x y hxy,
      apply funext,

      intro a',
      cases quot.exists_rep a' with a h_a, rw ← h_a,

      apply map.resp _ _,
      apply (holds_for_head_and_tail r).2,
      split,
      exact hxy,
      exact ref a,

    end
    omit ref

    -- thus we have a similar construction for the reduced map
    def reduce_towards_quotient:
    (n+1-var_map_to β) → (n-var_map_to (quot r → β)) := λ map, {
    f := quotient_off_head map,
    resp := quotient_is_respectful map}

    -- useful for rewriting
    protected lemma compute (f : (vector α n.succ) → β) : ∀ resp, ∀ {{head : α}} {{tail : vector α n}},
    (quotient_off_head {f := f, resp := resp}) tail (quot.mk r head) = f (head ::ᵥ tail) := λ _ _ _, rfl

    protected lemma compute_map (map : n+1-var_map_to β) : ∀ {{head : α}} {{tail : vector α n}},
    (quotient_off_head map) tail (quot.mk r head) = map.f (head ::ᵥ tail) := λ _ _, rfl

  end

  universe u -- induction is much happier dealing with one universe at a time!
  def lift_internal :Π
  (n : ℕ) (α : Type u) (r : rel α) (ref : reflexive r) (β : Type u)
  (map : @multivar_map _ r n β) (v : vector (quot r) n),
  (β)
  | 0     := λ _ _ _ _ map _, map.f nil
  | (n+1) := λ α _ ref _ map v, @lift_internal n α _ ref _ (reduce_towards_quotient ref map) v.tail v.head

end multi

namespace mquot
  open multi

  def mk {α : Type*} (r : rel α) {n : ℕ} :
  vector α n → vector (quot r) n :=
  λ v, map (quot.mk r) v

  theorem ind {α : Type*} {r : rel α} {n : ℕ}
  {β : vector (quot r) n → Prop} :
  (∀ a, β (mk r a)) → ∀ q, β q :=
  begin
    induction n with n h_ind,

    -- function in 0 variables:
    intros h _,
    rw unique.forall_iff at h,
    convert h,

    -- function in n+1 variables:
    intro h,
    apply (holds_for_all_heads_and_tails β).2,
    intro q,
    apply @h_ind (λ _, _),
    intro x,
    revert q,
    apply quot.ind,
    intro a,
    convert h (a ::ᵥ x),
    simp_rw [mk, map_cons],

  end

  universe u def lift {α : Type u} {r : rel α} {n : ℕ} {β : Type u} (f : (vector α n) → β) :
  reflexive r →
  (∀ a b : vector α n, (∀ i, r (a.nth i) (b.nth i)) → f a = f b) →
  (vector (quot r) n) → β :=
  λ ref h, lift_internal n α r ref β { f := f, resp := h }

  theorem sound {α : Type*} {r : rel α} {n : ℕ} {a b : vector α n} :
  (∀ i, r (a.nth i) (b.nth i)) → mk r a = mk r b :=
  begin
    intro h,
    apply ext,
    intro i,
    rw mk,
    simp,
    exact quot.sound (h i),
  end


  /- Analog of the formula `quot.lift f _ (quot.mk a) = f a`, which is baked into lean
  -- as a reduction rule, more primitive than an axiom even. Unfortunately the higher
  -- dimensional version does require a proof, and an annoying one at that.         -/

  @[simp] theorem comp {α : Type u} {r : rel α} {ref : reflexive r}
  {n : ℕ} {β : Type u} (f : (vector α n) → β) {{v : vector α n}} :
  ∀ h_resp, lift f ref h_resp (mk r v) = f v :=
  begin

    revert β,
    induction n with n h_ind,

    /- base case -/

    intros β f h_resp,
    simp_rw [lift, lift_internal],
    apply congr_arg,
    exact subsingleton.elim _ _,

    /- induction -/

    revert v,                                             -- break head off of vector
    rw holds_for_all_heads_and_tails,
    intros head tail,

    intros β func h_resp,                                 -- take parameters
    let map : multivar_map := {f := func, resp := h_resp},
    let reduced_map := quotient_off_head ref map,

    specialize @h_ind tail (quot r → β),                  -- find previous case
    specialize @h_ind (quotient_off_head ref map),
    specialize @h_ind (quotient_is_respectful ref map),

    simp_rw [lift, lift_internal, mk] at *,
    simp_rw [head_map, tail_map, head_cons, tail_cons],
    simp_rw [← multi.compute ref func h_resp],            -- match them up
    simp_rw [← map, ← reduced_map] at *,

    apply congr_fun,
    exact h_ind,                                           -- finish off

  end

end mquot

namespace mquotient
  open multi

  def mk {α : Type*} [s : setoid α] {n : ℕ} :
  vector α n → vector (quotient s) n :=
  λ v, map quotient.mk v

  theorem ind {α : Type*} [s : setoid α] {n : ℕ}
  {β : vector (quotient s) n → Prop} :
  (∀ a, β (mk a)) → ∀ q, β q := mquot.ind

  universe u def lift {α : Type u} [s : setoid α] {n : ℕ} {β : Type u} (f : (vector α n) → β) :
  (∀ a b : vector α n, (∀ i, setoid.r (a.nth i) (b.nth i)) → f a = f b) →
  (vector (quotient s) n) → β :=
  λ h, lift_internal n α setoid.r setoid.iseqv.left β { f := f, resp := h }

  theorem sound {α : Type*} [s : setoid α] {n : ℕ} {a b : vector α n} :
  (∀ i, setoid.r (a.nth i) (b.nth i)) → mk a = mk b := mquot.sound

  @[simp] theorem comp {α : Type u} [s : setoid α]
  {n : ℕ} {β : Type u} (f : (vector α n) → β) {{v : vector α n}} :
  ∀ h_resp, lift f h_resp (mk v) = f v := λ h_resp, mquot.comp f h_resp

end mquotient
