import hom

namespace UA
  universe u_lang

  section
    universe u_t
    parameter [σ : signature.{u_lang}]


    /- *** `word` means an expression in the language of `σ`, with variables from `T` *** -/

    inductive word (T : Type u_t) : Type (max u_lang u_t)
    | var           : T → word
    | opr (f : σ.F) : (fin (arity_of f) → word) → word

    def vars {T : Type u_t} : word T → set T
    | (word.var t)     := {t}
    | (word.opr f xxx) := ⋃ i, vars (xxx i)

    theorem finitely_many_vars {T : Type u_t} (w : word T) : set.finite (vars w) :=
    begin
      induction w,

      rw vars,
      apply set.to_finite,

      apply set.finite_Union,
      assumption,
    end


    /- The words themselvs for a structure in the ovbious way. -/

    instance action_on_words (T : Type u_t) : action_on (word T) := λ f, word.opr f ∘ vector.nth

    def word_algebra (T : Type u_t) : Structure := ⟨word T, action_on_words T⟩

    @[simp] lemma action_of_word_algebra {T : Type u_t} {f www} :
    (word_algebra T).action f www = word.opr f www.nth := rfl

  end

  section
    universe u_str
    parameter [σ : signature.{u_lang}]
    include σ


    /- A `σ-structure` admits a canonical `evaluation` from its word algebra -/

    def eval {α : Type u_str} [act : action_on α] : word α → α
    | (word.var t)    := t
    | (word.opr f xxx) := act f (vector.of_fn (λ i, eval (xxx i)))

    instance eval_is_hom {α : Type u_str} [act : action_on α] : homomorphism (@eval α _) :=
    begin
      intros f www,
      rw UA.action_on_words,
      simp_rw eval,
      congr,
      apply vector.ext,
      intro i,
      simp,
    end

    def evaluation {A : Structure.{u_lang u_str}} : Homomorphism (word_algebra A) A :=
    ⟨eval, eval_is_hom⟩

  end


  /- `translatation` is the process of substituting for the variables in a word -/

  section
    universes u_s u_t

    def translate [σ : signature.{u_lang}] {S : Type u_s} {T : Type u_t}
    (φ : S → T) : word S → word T
    | (word.var t)     := word.var (φ t)
    | (word.opr f xxx) := word.opr f (λ i, translate (xxx i))
  end

  /- *** Introduce notation out of sight of any parameters ***
  -- previously this was declared 'local', to depend on the parameter σ, but this
  -- seemed to create a mysterious problem where there were two σ's floating around -/
  postfix `†` : 110 := translate -- right value?


  section
    universes u_r u_s u_t u_strA u_strB
    parameter [σ : signature.{u_lang}]
    include σ


    /- *** do not put this lemma through `simp_rw`, as it hangs ***
    -- Should probably investigate at some point. Especially don't expose this to `simp`,
    -- for the same reason, though it isn't unequivocally a simplification anyway.     -/
    lemma translation_functorial
    {R : Type u_r} {S : Type u_s} {T : Type u_t} (ψ : R → S) (φ : S → T) (w : word R) :
    (φ ∘ ψ)† w = (φ†) (ψ† w) :=
    begin
      induction w,
      refl,
      simp_rw translate,
      simp_rw w_ih,
      simp,
    end


    /- The property of being a `homomorphism` is in fact characterised by the
    -- preservation of evaluations of *any* word in the language.          -/

    lemma hom_preserves_eval
    {α : Type u_strA} {β : Type u_strB} [actA : action_on α] [actB : action_on β]
    {φ : α → β}
    [H : homomorphism φ] {w : word α} : φ (eval w) = eval (φ† w) :=
    begin
      induction w with _ f www h_ind, {
        refl,
      },
      {
        specialize H f (vector.of_fn (eval ∘ www)),
        simp_rw [eval, ← H, vector.map_of_of_fn],
        rw (funext h_ind : φ ∘ eval ∘ www = λ i, eval (φ† (www i))),
        refl,
      },
    end

    lemma hom_iff
    {α : Type u_strA} {β : Type u_strB} [actA : action_on α] [actB : action_on β]
    {φ : α → β} :
    homomorphism φ ↔ ∀ w : word α, φ (eval w) = eval (φ† w) :=
    begin

      split,

      introI,
      intro word,
      exact hom_preserves_eval,

      intros h f xxx,
      specialize h (word.opr f (word.var ∘ xxx.nth)),
      simp_rw [eval, vector.of_fn_nth] at h,
      simp_rw [h, translate, eval],
      congr,
      apply vector.ext,
      intro i,
      simp_rw [vector.nth_of_fn, vector.nth_map],

    end

  end

end UA
