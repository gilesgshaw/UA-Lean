# Universal Algebra in Lean

This library is an attempt to realize the main definitions and theorems of universal algebra in lean.

Specifically, this is the general theory of algebraic objects affording the following:
- a language of (arbitrarily many) operation symbols of *finite* arity
- a theory of (arbitrarily many) axioms of the form ∀x...z f(x...z) = g(x...z), where f and g are composites of the operations

To clarify, we do *not* allow:
- relation symbols other than equality
- conditional equations (Horn clauses)

Nonetheless this encompasses at least groups, monoids, rings, modules, vector spaces, group representations, (lie) algebras, lattices... and variants of.

## Extracts

<!-- Process: {- The notion of [words](@@url_of('inductive word', 'src/words.lean')@@) in a given language.} -->
- The notion of [words](https://github.com/gilesgshaw/UA-Lean/blob/working/src/words.lean#L13) in a given language.
These are easily defined in lean thanks to the machinery of nested induction.
The words over a fixed set of variable form the 'freest' structure generated by that set.

<!-- Process: {- [Theorem:](@@url_of('lemma hom_iff', 'src/words.lean')@@)} -->
- [Theorem:](https://github.com/gilesgshaw/UA-Lean/blob/working/src/words.lean#L130)
a map between structures `φ : A → B` is a homomorphism if and only if for every word in the ambient language, having variables in `A`,
the evaluation of this word commutes with the application of `φ`. For instance in Galois theory, this says that morphisms over a ground field `k` preserve
the evaluation of polynomials with coefficients in `k`.

<!-- Process: {- [Defenition](@@url_of('def gen_by', 'src/cong.lean')@@) of the congruence generated by an arbitrary set of relations amongst the elements of a structure.} -->
- [Defenition](https://github.com/gilesgshaw/UA-Lean/blob/working/src/cong.lean#L176) of the congruence generated by an arbitrary set of relations amongst the elements of a structure.
By definition this is an equivalence relation modulo which there is a well defined quotient object.
Often a congruence is determined by the equiverlance class of a particular constant symbol, or 'kernel' - e.g. for groups, a normal subgroup.

<!-- Process: {- [Enforcement of axioms](@@url_of('def enforce_axioms', 'src/theory.lean')@@) - that is -} -->
- [Enforcement of axioms](https://github.com/gilesgshaw/UA-Lean/blob/working/src/theory.lean#L93) - that is -
the quotient object obtained by realizing all instances of the axioms of a theory in a given structure.
Together with the construction of word algebras, this produces in particular the notion of free objects and object presentations (e.g. of groups, modules... ).
Moreover, it allows us to define objects which are free with respect to an object from a different theory, for example,
   - the universal enveloping algebra of a lie algebra;
   - passing to rings of polynomials;
   - the abelianisation of group;
   - for a module, the extension of the ring of scalars.

## Source files

In order of dependence

| fin\  <br/> relation\ <br/> vector\         | background theory about the corresponding types in mathlib  								   		|
| :---					      | :---          									   	       	  			   		|
| multifunction.lean <br/> multiquotient.lean | multivariate quotients (i.e. being able lift a function of many variables to many corresponding quotients, in the spirit of `quot`) 	|
| basic.lean     			      | the basic theory of algebraic *operations*, including homomorphisms and substructures           			   		|
| cong.lean      			      | the theory of congruences (quotients) on algebraic structures                 			    			   		|
| words.lean    			      | the set of words in a given language, evaluation and translation maps, etc...                       			   		|
| theory.lean  				      | the basic theory of algebraic *axioms* 					      			    			   		|


## Terminology

A *signature*, or *language*, is a set of operation symbols with specified arities. The following definitions pertain to a given language:

| *structure*					| a 'medium' admitting an 'action' of the operations										|
| :---						| :---																|
| *word*					| a tree-like composite of the operations, whose 'leaves' are arbitrary variables (though indeed 0-ary symbols are also leaves)	|
| *evaluation*					| the natural process, applied to words over a given structure, of inductively applying the relevant actions			|
| *equation*					| formally, just a pair of words. given a structure, we imagine it to be the claim that they have the same evaluation		|
| *sentence*					| an equation whose variables are intended to be placeholders. formally we may just use the natural numbers.			|
| *translation*					| the process of substituting for each variable in a word									|
| *axiom*					| a sentence which is intended to be 'true' for all possible substitutions into a given structure				|

In a particular language, *theory* formally means just a set of axioms. The corresponding *variety* of algebras is simply the collection of those objects satisfying the axioms.
*Theory* may also refer to the set of all sentences which hold universally in a given variety.


