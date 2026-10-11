# Supplemental Artifact for *Context Types: Bunched Modalities for Unifying Safety and Reachability*

This repository is the Rocq proof artifact for the paper *Context Types:
Bunched Modalities for Unifying Safety and Reachability*.  It mechanizes the
core context-type calculus, its resource semantics, and the Fundamental
Theorem together with denotational soundness --- all stated
and proved for the paper's **nondeterministic** language (Section 5), which
includes generators and type-level persistence.  Because that development
subsumes the deterministic fragment of Sections 3--4 (every deterministic
term is a special case of the nondeterministic calculus, and the proofs
cover the corresponding typing rules), the same theorems also serve as a
mechanization of the deterministic metatheory.

The compiled development contains no `Admitted.`/`admit.` in Rocq source files.

## Getting Started

The recommended way to evaluate the artifact is with Docker.  The image fixes
the complete proof environment:

| Package | Version |
| --- | --- |
| OCaml | 4.14.4 |
| [Rocq](https://rocq-prover.org/) | 9.1.0 |
| [Rocq standard library](https://github.com/coq/stdlib) | 9.0.0 |
| [rocq-stdpp](https://gitlab.mpi-sws.org/iris/stdpp) | dev.2026-01-23.0.217a887d |

### Requirements

Install [Docker](https://docs.docker.com/get-docker/) and check that the daemon
is available with:

```bash
docker run --rm hello-world
```

The published image is built from Ubuntu 22.04.

### Using the Pre-Built Docker Image

Pull the pre-built artifact image from Docker Hub:

```bash
docker pull anonymousartifact/context-types:popl27
```

This is the recommended evaluation path.  The image already contains the
pinned dependencies and a compiled copy of every Rocq source file.

### Building the Docker Image (Optional)

Alternatively, rebuild the image from the supplied `Dockerfile` at the
repository root:

```bash
docker build --tag context-types:popl27 .
```

The Docker build installs the pinned dependencies and compiles every Rocq
source file.  It therefore already performs a complete proof check.  On an
ARM64 host with 8 Docker CPUs, the proof-compilation phase took roughly 2--3
minutes; a complete first image build took about 7 minutes 30 seconds,
including dependency downloads and installation.  Times will vary with the
host and network connection.

### Running the Docker Image

To enter the pre-built image at the artifact root, run:

```bash
docker run --rm -it anonymousartifact/context-types:popl27
```

If the image was built locally instead, run:

```bash
docker run --rm -it context-types:popl27
```

### Quick Artifact Check

The following non-interactive command checks the compiled development for
admitted proofs, prints the assumptions of the top-level theorems, and asks
Rocq's kernel checker to validate the complete soundness module:

```bash
docker run --rm anonymousartifact/context-types:popl27 make artifact-check
```

The command ends with:

```text
No Admitted./admit. commands found.
Kernel check completed successfully.
Artifact check completed successfully.
```

The checks can also be run separately while exploring the artifact:

```bash
# Show the exact compiler and library versions installed in the image.
make environment

# Search every Rocq source file for admitted proofs.
make check-admits

# Print the assumptions of the four top-level soundness theorems.
make print-assumptions

# Ask Rocq's kernel checker to validate the complete soundness module.
make kernel-check
```

The image includes `vim`, `less`, `ripgrep`, and `git` for source inspection.
For example, the theorem statements and their proof assumptions can be
inspected directly with:

```bash
vim ContextTyping/theories/Soundness.v
vim ContextTyping/theories/SoundnessAssumptions.v
make print-assumptions | less
```

To rebuild all proofs from scratch inside the image, use:

```bash
docker run --rm anonymousartifact/context-types:popl27 bash -lc \
  'make clean && make -j"$(nproc)" && make artifact-check'
```

Replace `anonymousartifact/context-types:popl27` with
`context-types:popl27` in these commands when using the locally built image.

The `GNUmakefile` generates Rocq's `Makefile.coq` automatically; reviewers do
not need to invoke `rocq makefile` directly.

## Evaluation Guide

The submitted artifact evaluates the mechanized metatheory claims of the
paper.  A complete clean build followed by `make artifact-check` checks all of
the following claims.  The later correspondence table gives precise source
locations for their definitions and supporting infrastructure.

| Claim | Paper | Artifact evidence | Evaluation |
| --- | --- | --- | --- |
| Context-logic satisfaction is Kripke monotone | Theorem 4.4 | `res_models_kripke` | Full build |
| The typing judgment satisfies its logical relation | Theorem 4.10 | `Fundamental` and `concrete_Fundamental` | Full build and printed assumptions |
| Closed well-typed programs satisfy their context types | Corollary 4.11 | `denotational_soundness` and `concrete_denotational_soundness` | Full build and printed assumptions |
| The nondeterministic calculus, generators, and type-level persistence are sound | Section 5 and Theorem 5.3 | The same top-level theorems instantiated with the concrete primitive context | Full build and printed assumptions |
| The mechanized definitions of universal quantification and persistence agree with their paper-style characterizations | Sections 4--5 | `res_models_forall_full_world_iff` and `res_models_persist_order_iff` | Full build |

No case-study formalization is included or claimed by this artifact; the
artifact is the complete mechanization of the core metatheory.

### Assumption Output

During the build, the final file
`ContextTyping/theories/SoundnessAssumptions.v` runs Rocq's
`Print Assumptions` on the top-level theorems:

```coq
From ContextTyping Require Import Soundness.

Print Assumptions Fundamental.
Print Assumptions denotational_soundness.
Print Assumptions concrete_Fundamental.
Print Assumptions concrete_denotational_soundness.
```

For example, `Print Assumptions Fundamental.` reports only standard logical
principles used by the development and its dependencies:

```text
Print Assumptions Fundamental.
Axioms:
PropExtensionality.propositional_extensionality :
  forall P Q : Prop, P <-> Q -> P = Q
ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
ClassicalEpsilon.constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

## Design Choices and Differences from the Paper

- The paper first introduces a restricted deterministic language (Sections
  3--4) and then presents its nondeterministic extension (Section 5).  This
  artifact implements the **full nondeterministic** language and context type
  system: nondeterministic operational semantics, generators `boolGen` and
  `natGen`, precise primitive-operation contracts, and type-level
  persistence.  The mechanized Fundamental Theorem and denotational
  soundness are proved in that nondeterministic setting (corresponding to
  the Section 5 metatheory).  They nevertheless also cover the deterministic
  fragment: the deterministic rules and denotations of Sections 3--4 arise
  as the special case without generators or persistence, and those cases are
  included in the same proof development.
- The checked core language is limited to `Unit`, `Bool`, and `Nat`; it does
  not include lists or trees.  These are straightforward datatype extensions
  of the core.  For this checked fragment, fully constructed datatype values
  `d \bar v` are represented by `constant` and injected into values by
  `vconst`.  The primitive operators include the usual unary operations
  such as `plus1`, `minus1`, and `eq0`, together with random generators such
  as `boolGen` and `natGen`.
- For simplicity, pattern matching only matches on Boolean discriminees.
  Pattern matching on natural numbers can be implemented by first testing
  whether the scrutinee is zero:

  ```text
  let cond = op_eq0 n in
  match cond with
  | true -> e1
  | false ->
      let m = op_minus1 n in
      e2
  ```
- Function-application typing rules in the artifact require the argument to be
  a fresh variable rather than an arbitrary value.  This is only a proof-facing
  normal form: an application `v1 v2` can be rewritten as
  `let x = ret v2 in v1 x` for a fresh `x`.  The restriction gives all
  application proofs the same argument shape and keeps the resource-splitting
  and result-extension arguments uniform.
- The paper presents match typing with a more general control-flow index `i`.
  The artifact splits the Boolean match rule into three constructors: only the
  first branch is reachable, only the second branch is reachable, or both
  branches are reachable.  There is no constructor for the case where neither
  branch is reachable, because every term accepted by the context type system
  is required to be total.
- The type system contains union types in addition to the constructs used in
  the paper examples.
- The logic does not include an existential formula constructor, because the
  checked denotation and soundness proof do not use one.
- The formalization follows
  [The Locally Nameless Representation](https://chargueraud.org/research/2009/ln/main.pdf):
  bound variables are represented de Bruijn-style and free variables by atoms.
  Consequently, binder-heavy definitions look slightly different from the
  paper's surface notation.
- Refinement propositions are shallowly embedded Coq propositions.  A
  qualifier is a semantic predicate together with an explicit support set, not
  a first-order syntax tree.  See Proof Details for the artifact-level
  treatment of qualifier support.

## Proof File Structures

The artifact is organized as a layered Rocq development:

```text
ContextBase
  -> ContextStore
  -> ContextAlgebra
  -> ContextLogic
  -> CoreLang
  -> ContextTypeLanguage
  -> ContextBasicDenotation
  -> Denotation
  -> ContextTyping
```

- `ContextBase`, `ContextStore`, and `ContextAlgebra` define atoms, logical
  variables, stores, and resources.  A store is the artifact name for the
  paper's environment: a finite map from variables to values.  Worlds,
  resources, and capabilities refer to the same semantic objects in this
  development.
- `ContextLogic` defines formulas, satisfaction, bunched connectives,
  fiber quantification, and persistence.
- `CoreLang` defines the core term language, basic typing, small-step
  semantics, and operational result facts.
- `ContextTypeLanguage` defines context types, contexts, erasure,
  locally nameless operations, and well-formedness.
- `ContextBasicDenotation` defines formula atoms for basic worlds, basic
  typing, term totality/results, qualifiers, and relevant environments.
- `Denotation` defines type/context denotation, constants, result-first
  Arrow/Wand support, let transport, and primitive-operation denotation
  support.
- `ContextTyping` defines primitive-operation contexts, typing rules, and the
  soundness proof for the nondeterministic system.  The main soundness proof
  is split by typing-rule families, with separate files for lambdas,
  applications, match, recursion, and persistence; the deterministic
  fragment is covered as the special case of these proofs.

## Paper-to-artifact Correspondence

| Definition/Theorems | Paper | Definition | Notation |
| --- | --- | --- | --- |
| Store/environment | Definition D.1 in appendix | Stores (`Store`, `LStore`) in `ContextStore/StoreInterface.v` (lines 15 and 16); restriction and compatibility notations in the same file (lines 48-51) | `σ ↾ X`, `σ1 ##ₛ σ2`, map notation `<[x := v]> σ`, `σ !! x` |
| Capability/resource/world | Definition 4.1, Definition D.2 in appendix | Worlds/resources (`World`, `WfWorld`) in `ContextAlgebra/theories/ResourceInterfaceCore.v` (lines 20 and 21); domain, stores, restriction, unit, and their notations in the same file (lines 30-69) | `𝟙`, `Dom m`, `m ↾ X`, `m ⊑ᵣ n` |
| Fiber | Definition 4.2 | Fiber/projection operations in `ContextAlgebra/theories/ResourceInterfaceCore.v` (lines 605-608) | `fiber(mfib, m, X, σ)`, `mfib ∈ᶠ Fiber(m, X)` |
| Resource algebra operations | Sec. 4.2, Definitions D.3–D.5 in appendix | Abstract algebra class (`ContextAlgebra`) in `ContextAlgebra/theories/ResourceAlgebra.v` (line 13); concrete compatibility/product/sum/subset in `ContextAlgebra/theories/ResourceInterfaceCore.v` (lines 443-451) | `m1 ##ᵣ m2`, `m1 ×[H] m2`, `m1 +[H] m2`, `m1 ⊆ᵣ m2` |
| Formula syntax | Definition 4.3 and Sec. 5 | Formula syntax (`Formula`) in `ContextLogic/theories/FormulaSyntaxCore.v` (line 21) | `⊤`, `⊥`, `@atom q`, `P ∧ Q`, `P ∨ Q`, `P → Q`, `P ∗ Q`, `P -∗[d] Q`, `P ⊕ Q`, `∀. P`, `over P`, `under P`, `□ P`, `fib D |> P` |
| Formula satisfaction | Definition 4.3 and persistence in Sec. 5 | Satisfaction (`res_models`) in `ContextLogic/theories/FormulaSemantics.v` (line 894) | `m ⊨ P` |
| Entailment and equivalence | Definition 4.3 | Entailment (`entails`) in `ContextLogic/theories/FormulaSemantics.v` (line 913); formula equivalence (`formula_equiv`) and the corresponding notations in `ContextLogic/theories/FormulaConnectivesHigher.v` (lines 817-823) | `P ⊫ Q`, `P ⊣⊢ Q` |
| Kripke monotonicity | Theorem 4.4 | `res_models_kripke` in `ContextLogic/theories/FormulaSemantics.v` (line 917) | `m ⊑ n -> m ⊨ P -> n ⊨ P` |
| Core base types and primitive operations | Core language syntax (Fig. 1) | Basic types (`base_ty`) in `CoreLang/theories/Syntax.v` (line 14); primitive operations (`prim_op`) in `CoreLang/theories/Syntax.v` (line 45) | `Unit`, `Bool`, `Nat`, `T1 →ₜ T2`, `op_eq0`, `op_plus1`, `op_minus1`, `op_boolGen`, `op_natGen` |
| Term syntax | Core language syntax (Fig. 1) | Mutually recursive values (`value`) and expressions (`tm`) in `CoreLang/theories/Syntax.v` (lines 76 and 83) | `ret v`, `let: e1 in e2`, `v1 · v2`, `if v then et else ef` |
| Operational semantics | Fig. 9 in appendix | Small-step relation (`step`) in `CoreLang/theories/SmallStep.v` (line 99) | `step e e'` |
| Basic typing | Fig. 11 in appendix | Basic typing judgments (`value_has_type`, `tm_has_type`) in `CoreLang/theories/BasicTyping.v` (lines 35 and 51) | `Γ ⊢ᵥ v ⋮ T`, `Γ ⊢ₑ e ⋮ T` |
| Qualifiers | Type syntax (Fig. 2) | Semantic qualifiers (`tqual D P`) in `ContextQualifier/theories/Qualifier.v` (line 26); equality qualifier (`mk_q_eq`) in `ContextTypeLanguage/theories/Syntax.v` (line 388) | Shallow Coq propositions with explicit support |
| Context type syntax | Type syntax (Fig. 2) | Context types (`context_ty`) in `ContextTypeLanguage/theories/Syntax.v` (line 26) | `{: b | φ }`, `[: b | φ ]`, `τ1 ⊓ τ2`, `τ1 ⊔ τ2`, `τ1 ⊕ τ2`, `τx → τ`, `τx -∗ τ`, `□ τ` |
| Type context syntax | Type syntax (Fig. 2) | Contexts (`ctx`) in `ContextTypeLanguage/theories/Syntax.v` (line 36) | `Emp`, `x ∷ τ`, `Γ1 ,, Γ2`, `Γ1 ∗ Γ2`, `Γ1 ⊕ Γ2` |
| Type erasure | Fig. 10 in appendix | Type erasure (`erase_ty`) and context erasure (`erase_ctx`) in `ContextTypeLanguage/theories/Syntax.v` (lines 254 and 272) | `⌊τ⌋`, `⌊Γ⌋` |
| Term-denotation and guard formulas | Sec. 4.4, Type Denotation and Soundness, first paragraph: denotation of a term `e`, basic typing, and totality guards | Result formula (`expr_result_formula_at`) in `ContextBasicDenotation/theories/TermOpen.v` (line 19); total formula (`expr_total_formula`) in `ContextBasicDenotation/theories/TermEval.v` (line 1114); basic typing formula (`expr_basic_typing_formula`) in `ContextBasicDenotation/theories/BasicTypingFormula.v` (line 954); world/guard formulas (`basic_world_formula`, `ty_guard_formula`, `ty_static_guard_formula`) in `ContextBasicDenotation/theories/StoreTyping.v` (line 50) and `Denotation/theories/TypeDenote.v` (lines 10 and 16) | `FResult[D ⊢ e ⇓ x]`, `FTotal[e]`, `FHasType[Σ ⊢ e ⋮ T]`, `FWorld[Σ]`, `guard[Σ; τ; e]`, `static_guard[Σ; τ; e]` |
| Type denotation | Definition 4.7, Definition 5.2, and Sec. 5.2 | Gas-indexed type denotation (`ty_denote_gas`) in `Denotation/theories/TypeDenote.v` (line 141); saturated denotation (`ty_denote`) in `Denotation/theories/TypeDenote.v` (line 204) | `⟦ty τ⟧[Σ, gas] e`, `⟦ty τ⟧[Δ] e`, `TyDenote[Δ; τ; e]` |
| Type context denotation | Definition 4.8 | Context denotation (`ctx_denote_under`) in `Denotation/theories/Context.v` (line 17) | `⟦ctx⟧[Σ] Γ` |
| Well-founded recursive-call relation | Fig. 4, T-Fix rule | Base-value order (`constant_lt_for_base`) in `ContextTypeLanguage/theories/Syntax.v` (line 412); recursive-call argument type (`fix_rec_call_ty`) in the same file (line 450); used by T-Fix in `ContextTyping/theories/Typing.v` | `c1 ≺[b] c2`, `fix_rec_call_ty b y τx τ` |
| Typing judgment | Fig. 4 and Sec. 5.1 | Context typing judgment (`has_context_type`) in `ContextTyping/theories/Typing.v` (line 108) | `Γ ⊢ᶜ [Φ; Σ] e ⋮ τ` |
| Typing well-formedness | Fig. 3, Fig. 12–13 in appendix | Well-formedness (`context_typing_wf`) in `ContextTyping/theories/Typing.v` (line 67) | `Γ ⊢wf[Σ] e ⋮ τ` |
| Semantic type subsumption | Fig. 5 | Semantic subtype (`sub_type_under`) in `ContextTyping/theories/Typing.v` (line 45) | `Γ ⊢ᶜ τ1 ≤[Σ] τ2` |
| Semantic context subsumption | Fig. 5 | Semantic context subtype (`ctx_sub_under`) in `ContextTyping/theories/Typing.v` (line 55) | `Γ1 ≤ᶜ[Σ; X] Γ2` |
| Primitive-operation context | Definition 4.9 | Primitive signature (`primop_sig`) and context (`primop_ctx`) in `ContextTyping/theories/PrimOpContext.v` (lines 18 and 31); well-formedness (`wf_primop_ctx`) in `ContextTyping/theories/PrimOpContext.v` (line 58) | `wf_primop_ctx Φ` |
| Concrete primitive context | Concrete instance of Definition 4.9 | Concrete context (`concrete_Φ`) in `ContextTyping/theories/PrimOpConcreteContext.v` (line 173); well-formedness theorem (`concrete_Φ_wf`) in `ContextTyping/theories/PrimOpConcreteContext.v` (line 1405) | `concrete_Φ` |
| Fundamental theorem (nondeterministic system) | Theorem 4.10 (deterministic statement in the paper); mechanized for the Section 5 nondeterministic calculus, which subsumes Theorem 4.10 | `Fundamental` in `ContextTyping/theories/Soundness.v` (line 972); concrete wrapper `concrete_Fundamental` in the same file (line 1149) | `Γ ⊢ᶜ [Φ; Σ] e ⋮ τ -> ⟦ctx⟧[Σ] Γ ⊫ ...` |
| Denotational soundness (nondeterministic system) | Corollary 4.11 / Theorem 5.3; mechanized for the Section 5 nondeterministic calculus (covers the deterministic closed-program corollary as a special case) | `denotational_soundness` in `ContextTyping/theories/Soundness.v` (line 1076); concrete wrapper `concrete_denotational_soundness` in the same file (line 1156) | closed programs have a result world satisfying `TyDenote[...]`; concrete versions instantiate `Φ := concrete_Φ` |

The mechanized Fundamental Theorem and denotational soundness are stated for
the nondeterministic language of Section 5.  Instantiating them to programs
that do not use generators or persistence recovers the deterministic
metatheory of Sections 3--4 (Theorem 4.10 and Corollary 4.11); the same
development therefore also serves as a formalization of that fragment.

The artifact defines universal quantification and persistence in forms that
are slightly different from the paper presentation because these definitions
are more convenient for the mechanized proof.  The bridge theorems are listed
in Proof Details below.

## Proof Details

### Logic formulas

`FFibVars D P`, written `fib D |> P`, is the artifact's multi-variable form
of the Binding Reference Operator from Definition 4.3.  It evaluates `P` on
the fibers induced by the variables in `D`.

The notation

```coq
m #> F ~~> mx
```

means that `F` is a resource extension function applicable to `m`, and `mx` is
the resource obtained by applying `F` to every store/environment in `m`.  A
typical example is the result extension for `[[e -->* x]]`: it maps each store
in the current capability to stores where the fresh variable `x` records a
value that `e` can reduce to in that store.  Thus the current capability `m`
is extended to `mx`, where `x` stores the possible results of `e` across the
stores in `m`.

`FForall P`, written `∀. P`, is implemented using explicit resource
extensions.  Intuitively, for every fresh name `y`, the artifact considers
every minimal extension of the current resource that provides exactly the
variables needed to interpret the opened body and outputs the fresh result
slot `y`; the opened body must hold on every such minimal extension.  The
locally nameless details
`exists L : aset, forall y : atom, y ∉ L ->` and
`formula_open 0 y φ` are the usual freshness/opening noise: semantically, this
matches the quantification described in the paper.  The full-world
characterization used by many later proofs is an iff:

```coq
Lemma res_models_forall_full_world_iff
    (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) ->
  (m ⊨ FForall φ <->
    exists L : aset,
      forall y : atom, y ∉ L ->
        forall my : WfWorldT,
          world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
          res_restrict my (world_dom (m : WorldT)) = m ->
          my ⊨ formula_open 0 y φ).
```

This theorem is in
`ContextLogic/theories/FormulaConnectivesHigher.v` (line 621).

`FPersist P`, written `□ P`, is implemented similarly by using the smallest
singleton resource needed to model `P`.  The definition projects the current
resource to the support of `P` and requires this projection to be a singleton
resource satisfying `P`.  By `res_models_minimal_on`, this is equivalent to
the paper-style characterization: `r |= □P` iff there is a singleton resource
`{σ}` such that `{σ} ⊑ r` and `{σ} |= P`.

```coq
Lemma res_models_persist_order_iff (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FPersist φ <->
  exists σ : Store (V := V),
    let σw :=
      (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) in
    σw ⊑ m /\ σw ⊨ φ.
```

This theorem and the persistence algebra lemmas below are in
`ContextLogic/theories/FormulaConnectivesHigher.v` (lines 904, 949, 958, and
988, respectively).

The algebraic behavior used in the paper is then recovered by:

```coq
Lemma persistent_formula_equiv_persist (φ : FormulaT) :
  persistent_formula φ ->
  φ ⊣⊢ FPersist φ.

Lemma persistent_star_self (φ : FormulaT) :
  persistent_formula φ ->
  FStar φ φ ⊣⊢ φ.

Lemma persistent_star_and (φ ψ : FormulaT) :
  persistent_formula φ ->
  FStar φ ψ ⊣⊢ FAnd φ ψ.
```

The magic wand also has a more explicit locally nameless shape.  In the paper
notation `P -* Q`, the consequent `Q` may mention variables introduced by the
antecedent `P`; this is direct with named variables.  In locally nameless
syntax, both `P` and `Q` may contain bound variables, so the artifact records
how many binders from `P` remain in scope when opening the wand body.  Thus the
constructor is `FBWand d P Q`, written `P -∗[d] Q`, where the binder-depth
parameter `d` is an offset.  In ordinary value-level uses, `d = 1`; nested
result-first definitions may require the depth to be stated explicitly.

The proof repeatedly uses the fact that formula satisfaction depends only on
the free variables of the formula:

```coq
Lemma res_models_minimal_on (S : aset) (m : WfWorldT) (φ : FormulaT) :
  formula_fv φ ⊆ S →
  res_models m φ ↔ res_models (res_restrict m S) φ.
```

### Qualifier embedding

Refinement qualifiers are shallowly embedded as Coq propositions.  This lets
the artifact use the full expressiveness of `Prop` for the rich predicates
needed by type denotation, including basic well-typedness and totality
properties, without being limited by a first-order qualifier syntax.
Concretely, a qualifier is a support set of logical variables together with a
Coq predicate over stores whose domain is exactly that support:

```coq
Record qualifier : Type := tqual {
  qual_lvars : lvset;
  qual_prop : LStoreOnT qual_lvars -> Prop;
}.
```

This definition appears in `ContextQualifier/theories/Qualifier.v` (line 26).

The explicit support also gives the artifact precise control over which
variables a qualifier can observe.  For example, `top[x]` and `top[x,y]` are
not interchangeable: the former ranges over all values of `x`, while the
latter ranges over joint assignments to both `x` and `y`.  This distinction is
usually invisible in logics that use only overapproximate semantics, but it is
important for the precise over/under semantics used here.

Because qualifiers themselves are untyped, a bare top qualifier would range
over all syntactic values.  Thus `[v : Bool | top]` would otherwise also try to
cover natural numbers.  The type denotation fixes this at the embedding point by
building a typed qualifier atom.  The helper `typed_result_qual b φ` conjoins
the shallow qualifier predicate with a base-typing check for the result slot
inside the exact atom itself.  The helper definitions are in
`Denotation/theories/TypeDenote.v` (lines 86-102), and the expanded
`CTOver`/`CTUnder` branches in `ty_denote_gas` show where that typed atom is
used (lines 150-159):

```coq
Definition result_basic_typing_formula (b : base_ty) : FormulaT :=
  FHasType[(∅ ▷ TBase b)%lvar ⊢ (ret # 0)%core ⋮ TBase b].

Definition typed_result_qual (b : base_ty) (φ : type_qualifier) : type_qualifier :=
  tqual (qual_vars φ ∪ {[LVBound 0]})
    (fun s =>
      qual_prop φ
        (lstore_on_restrict (qual_vars φ) s ltac:(set_solver)) /\
      exists v,
        (lso_store s : LStoreT) !! LVBound 0 = Some v /\
        basic_value_has_ltype (∅ : lty_env) v (TBase b)).

Definition over_result_body (b : base_ty) (φ : type_qualifier) : FormulaT :=
  (over (@atom (typed_result_qual b φ)))%formula.

Definition under_result_body (b : base_ty) (φ : type_qualifier) : FormulaT :=
  (under (@atom (typed_result_qual b φ)))%formula.
```

### Type denotation

The formula layer proves that satisfaction is determined by the projection of
the resource to the free variables of the formula:

```coq
Lemma res_models_minimal_on (S : aset) (m : WfWorldT) (φ : FormulaT) :
  formula_fv φ ⊆ S →
  res_models m φ ↔ res_models (res_restrict m S) φ.
```

This theorem appears in `ContextLogic/theories/FormulaSemantics.v` (line
941).  The type denotation is designed so that the same idea is available for
the logical relation.  At the beginning of the `ty_denote_gas` fixpoint, the
environment is clipped to the variables relevant to the term `e` and type
`τ`:

```coq
Fixpoint ty_denote_gas
    (gas : nat) (Σ : lty_env) (τ : context_ty) (e : tm)
    {struct gas} : FormulaT :=
  let Σg := relevant_env Σ τ e in
  (guard[Σg; τ; e] ∧ ...)%formula.
```

The clipping loses no semantic information.  It makes the type-denotation
support theorem precise: whether `m` satisfies `[[τ]] e` depends only on the
projection of `m` to the free variables of `τ` and `e`.

```coq
Lemma ty_denote_gas_minimal_on gas Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ e <->
  res_restrict m (fv_tm e ∪ fv_cty τ) ⊨ ty_denote_gas gas Σ τ e.
```

This theorem is in `Denotation/theories/TypeDenoteRegular.v` (line 2018).

As in the paper, type denotation always includes the ordinary well-formedness,
well-typedness, and totality obligations.  These are encoded in the guard, and
the guard is conjoined at the start of every `ty_denote_gas` unfolding:

```coq
Definition ty_guard_formula
    (Σ : lty_env) (τ : context_ty) (e : tm) : FormulaT :=
  (FWfTy[Σ; τ] ∧
    (FWorld[Σ] ∧
      (FHasType[Σ ⊢ e ⋮ (⌊τ⌋)%cty] ∧ FTotal[e])))%formula.
```

The guard definition is in `Denotation/theories/TypeDenote.v` (line 10), and
the fixpoint begins with `guard[Σg; τ; e] ∧ ...` in the same file (lines
141-145).

The paper encodes these side conditions as
`{Dom(Σ)} |> Atom(...)`: the binding-reference operator first fixes the
variables in `Σ`, and only then evaluates the exact atom.  In the artifact
this pattern is packaged as the abbreviation `FFiberAtom` (`fiber_atom q`):

```coq
Definition FFiberAtom (q : qualifier) : Formula :=
  FFibVars (qual_vars q) (FAtom q).
(* fiber_atom q  ≜  fib (qual_vars q) |> @atom q *)
```

`FFiberAtom` is defined in
`ContextLogic/theories/FormulaSyntaxCore.v` (line 111), and its notation is
declared in `ContextLogic/theories/FormulaNotation.v` (line 21).  Concrete
instances can be found in `StoreTyping.v`, `BasicTypingFormula.v`, and
`TermEval.v`.

The guard conjuncts above are all instances of this sugar:
`FWorld[Σ]`, `FWfTy[Σ; τ]`, `FHasType[Σ ⊢ e ⋮ ⌊τ⌋]`, and `FTotal[e]`
are each defined as `FFiberAtom` of an appropriate qualifier.
Unlike the paper's single combined atom, the mechanization splits the guard
into four such fiber-atoms and conjoins them.

### Typing proof core lemmas

Two denotation-transport lemmas carry much of the typing proof.

The first one is the let-introduction transport lemma.  It states that, after
extending a resource with the result graph of `e1` at a fresh slot `x`, the
opened body `e2 ^^ x` and the actual `let` term satisfy the same type
denotation at every gas level:

```coq
Lemma tlet_intro_denotation
    gas (Σ : lty_env) τ e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty τ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
  mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x) <->
  mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2).
```

This theorem is in `Denotation/theories/TypeEquivTLet.v` (line 1469).  It is
the core proof bridge for the `let` typing rules: soundness first constructs
the result-extension world, proves the body there, and then uses this theorem
to return to the source `let` term.

The second one says that type denotation is invariant under term-result
equivalence:

```coq
Definition typed_total_equiv_on
    (Σ : lty_env) (τ : context_ty) (m : WfWorldT)
    (e1 e2 : tm) : Prop :=
  tm_equiv_on m e1 e2 /\
  tm_total_equiv_on m e1 e2 /\
  m ⊨ ty_denote_gas 0 Σ τ e1 /\
  m ⊨ ty_denote_gas 0 Σ τ e2.

Lemma ty_denote_gas_tm_equiv
    gas Σ τ e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas gas Σ τ e1 ->
  m ⊨ ty_denote_gas gas Σ τ e2.
```

The premise is defined in `Denotation/theories/TypeEquivTermBase.v` (line 68),
and the transport theorem is in `Denotation/theories/TypeEquiv.v` (line 622).
This lemma lets the fundamental proof change the shape of a term without
changing its denotation.  For example, the match proof first relates a reachable
branch to the whole boolean match term (`SoundnessMatch.v`, line 264), the
lambda proof relates a beta-reduced body to an application of a lambda
(`SoundnessLam.v`, line 781), and the fix proof relates an application of a fix
value to the unfolded recursive body using `fix_tapp_unfold_tm_equiv_on`
(`SoundnessFixBase.v`, line 834) and `ty_denote_gas_tm_equiv` (line 998).

In a deterministic language, this kind of term-equivalence transport can often
derive the let-introduction transport: the result slot inserted by the
extension is the unique result obtained by re-running the term.  In the
nondeterministic language, that invariant breaks.  Concretely, let `m` be the
singleton world `{ σ0 }`, where `σ0` is the empty store.  Let
`e1 = boolGen unit` and `e2 = ret (vbvar 0)`.  The result extension
`m #> [[e1 --* x]] ~~> mx` can produce the world

```text
mx = {
  σF = { x ↦ false },
  σT = { x ↦ true  }
}.
```

Now `e2 ^^ x` is `ret x`.  Its result graph to a fresh output slot `y` preserves
the value already stored at `x`, so it produces exactly the diagonal stores

```text
{
  { x ↦ false, y ↦ false },
  { x ↦ true,  y ↦ true  }
}.
```

By contrast, `let x = e1 in ret x` re-runs `boolGen unit` in each store of
`mx`.  Starting from either `{ x ↦ false }` or `{ x ↦ true }`, the inner
generator can return either boolean, so its result graph to `y` produces

```text
{
  { x ↦ false, y ↦ false },
  { x ↦ false, y ↦ true  },
  { x ↦ true,  y ↦ false },
  { x ↦ true,  y ↦ true  }
}.
```

The two result graphs are therefore not equivalent even on the observable
variables `{x, y}`.  This is one of the places where the nondeterministic proof
diverges from the deterministic invariants and requires a separate
`tlet_intro_denotation` theorem.
