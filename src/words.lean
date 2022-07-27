import cong

namespace UA
  section
    parameter {σ : signature}


    /- *** `word` means an expression in the language of `σ`, with variables from `T` *** -/

    inductive word (T : Type*)
    | var           : T → word
    | opr (f : σ.F) : (fin (arity_of f) → word) → word

    def vars {T : Type*} : word T → set T
    | (word.var t)     := {t}
    | (word.opr f xxx) := ⋃ i, vars (xxx i)



    theorem finitely_many_vars {T : Type*} (w : word T) : set.finite (vars w) :=
    begin
      induction w,

      rw vars,
      apply set.to_finite,

      apply set.finite_Union,
      assumption,
    end


    /- The words themselvs for a structure in the ovbious way. -/

    def word_algebra (T : Type*) : σ-struct := {
    medium := word T,
    action := λ f, word.opr f ∘ vector.nth}

    @[simp] lemma action_of_word_algebra {T : Type*} {f www} :
    (word_algebra T).action f www = word.opr f www.nth := rfl


    /- A `σ-structure` admits a canonical `evaluation` from its word algebra -/

    def eval {A : Type*} [act : @structure_on σ A] : word A → A
    | (word.var t)    := t
    | (word.opr f xxx) := act f (vector.of_fn (λ i, eval (xxx i)))

    def evaluation {A : σ-struct} : homomorphism (word_algebra A) A := {
    func := eval,
    resp_ops := begin
      intros f www,
      rw action_of_word_algebra,
      simp_rw eval,
      congr,
      apply vector.ext,
      intro i,
      simp,
    end
    }


    /- `translatation` is the process of substituting for the variables in a word -/

    def translate {S : Type*} {T : Type*} (φ : S → T) : word S → word T
    | (word.var t)    := word.var (φ t)
    | (word.opr f xxx) := word.opr f (λ i, translate (xxx i))

    local postfix `*` :110 := translate


    /- The property of being a `homomorphism` is in fact characterised by the
    -- preservation of evaluations of *any* word in the language.          -/

    lemma hom_iff {A : σ-struct} {B : σ-struct} {φ : A → B}
    : preserves_σ φ ↔ ∀ w : word A, φ (eval w) = eval (φ* w) :=
    begin

      split,
      intros h w,
      induction w with _ f www h_ind,
      refl,
      rw eval,
      specialize h f,
      simp at h_ind,

      change (φ (A f (vector.of_fn (eval ∘ www))) = eval (translate φ (word.opr f www))),
      change (∀ (input : vector ↥A (arity_of f)), B f (vector.map φ input) = φ (A f input)) at h,
      change (∀ i, φ ((eval ∘ www) i) = eval (translate φ (www i))) at h_ind,

      specialize h (vector.of_fn (eval ∘ www)),
      rw ← h,
      rw vector.map_of_of_fn,

      have temp_lem : φ ∘ eval ∘ www = λ i, eval (translate φ (www i))
      := funext h_ind,
      rw temp_lem,

      change (B f (vector.of_fn (eval ∘ (λ i, (translate φ (www i)))))
      = eval (translate φ (word.opr f www))),
      simp_rw translate,
      simp_rw eval,
      refl,

      intros h f xxx,
      specialize h (word.opr f (word.var ∘ xxx.nth)),
      simp_rw eval at h,
      simp at h,
      rw UA.Structure_to_structure_on at h,
      rw h,
      simp_rw translate,
      simp_rw eval,

      congr,
      apply vector.ext,
      intro i,
      simp,

    end

  end

  postfix `-word`:40 := @word
  postfix `*` :110 := translate -- maybe I've misunderstood by setting this value high...

end UA
