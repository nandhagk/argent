# Argent design note

This note is for people who maintain Argent, or who want to judge what its bounds mean. It
explains why Argent derives time functions from plain Gallina, how the translation works, why
the derived costs match the extracted program, how a project can enforce their use, and what
the design can't do.

## 1. Decision

Argent follows the time-function method of Nipkow and others [1], ported to Rocq with
rocq-elpi. Programs are plain Gallina. For each executable definition `f`, an Elpi command
reads the kernel term of `f` and defines a separate, transparent constant `T_f` with values in
`N`. A generic component is a functor whose signature carries a time layer next to its
functional layer.

The method meets these requirements:

- **Charges can't be misplaced.** `T_f` is computed from the body of `f`, so a different charge
  needs a different program. `TimeFun` derives again any time function that it finds next to a
  callee before it uses it, `TimeCheck` derives a stored time function again, and `TimeAudit`
  checks that every executable constant reachable from a root has one.
- **Published theorems are 𝑂 statements**, and internal lemmas use named constants.
- **Bounds hold for the extracted program.** `T_f` counts call-by-value work up to a constant
  factor (section 4), so a bound that is proved tight is tight for the extracted program. Loop
  bounds come from a potential, so they depend neither on fuel nor on an accessibility proof.
- **Amortised bounds are cheap to prove.** They need one inequality per operation, one lemma for
  sequences and one lemma for loops.
- **Derivation is automatic**, and the tactic `time_step` closes most per-operation bounds in one
  line.
- **Module parameters work.** A call `M.op` is charged with `M.T_op`, which the signature
  declares.
- **No axioms and one dependency.** The only dependency is rocq-elpi. Signature contracts are
  `Parameter`s of module types, which every instance proves, so no axiom is added.
- **Code contains no accounting**, so tests and extraction are unchanged. The accessibility loop
  extracts to `let rec loop step s = match step s with Inl s0 -> loop step s0 | Inr r -> r`.

The alternatives that we considered each lose some of these properties.

| Alternative | What it loses |
| --- | --- |
| A writer monad that counts ticks, with charges placed by hand | Every function has a costed twin and an equation relating the two, and a lint must check where the charges are. Proofs about values see the monad. |
| A monad whose cost lives in a `Prop` index [2] | Programs stay monadic, and charges are placed by hand. |
| A functor over an abstract monad, instantiated at the identity and at a counter | Code stays monadic, and Rocq has no parametricity theorem to relate the two instances. |
| A translator in Ltac2 | Ltac2 has no command API and no persistent database, and building `match` and `fix` terms is fragile. Elpi binds variables in higher-order abstract syntax, and it is packaged. |
| Certifying extraction to the weak call-by-value λ-calculus L [3] | Its cost model is reasonable only up to a polynomial, so it is not tight for data structures. |
| Time credits in CFML or Iris [4, 5] | They verify OCaml or HeapLang programs, not Gallina. |
| Calf, Liquid Haskell `RTick`, RaML [6, 7, 8] | They need another proof assistant, ticks placed by hand, or an uncertified analysis. |

## 2. The translation

### Two examples

`append` is a structural recursion with no function arguments:

```coq
Fixpoint append {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: r => x :: append r l2
  end.
```

`TimeFun append` keeps the `fix` and the `match`, puts `1 +` in front of the body for the call
itself, replaces the recursive call by a call of the time function, and drops everything that
costs nothing (the constructor `::`, the variables):

```text
T_append =
fix T_append (A : Type) (l1 l2 : list A) {struct l1} : N :=
  (1 + match l1 with
       | [] => 0
       | _ :: r => T_append A r l2
       end)%N
```

`map` takes a function. Its time function takes a companion `T_f` right after `f`, and charges
each call `f x` with `T_f x`:

```text
T_map =
fix T_map (A B : Type) (f : A -> B) (T_f : A -> N) (l : list A) {struct l} :
    N :=
  (1 + match l with
       | [] => 0
       | x :: r => T_f x + T_map A B f T_f r
       end)%N
```

A caller of `map` builds the companion from its own argument. For the closure
`fun m => (n + m)%nat`, the companion is `1` for the call of the closure plus the cost of its
body:

```text
T_add_to_all =
fun (n : nat) (l : list nat) =>
(1 + T_map (fun m : nat => (n + m)%nat) (fun H : nat => 1 + Nat.T_add n H) l)%N
```

The rules below say this precisely. `T⟦e⟧ : N` is the cost of evaluating `e` by call-by-value.
`F⟦e⟧` is the time function of a function-valued `e`, and `C⟦e⟧` is the cost of creating the
closure `e`. Every `0`, `1` and `+` in the rules is in `N`.

### Shapes

Every binder and argument position of type `D` has a shape, which decides how the translation
treats it. Shapes are computed on the generic type of the callee, under its earlier binders, so
that they agree with the type of the callee's time function.

- **Irrelevant.** `D` is an arity (it ends in a sort), or `D` lives in `Prop` or `SProp`. Types,
  proofs and predicates are copied as they are, cost 0 and get no companion. For example,
  `A : Type` in `append`, and the proof argument `h : y < x` of a recursive call in a `Fix`.
- **Function.** The weak head normal form of `D` is a product, and `D` is not irrelevant. The
  argument gets a companion time function right after it, and the shape records the shapes of
  the binders of `D`. For example, `f : A -> B` in `map`, whose companion is `T_f : A -> N`.
- **Data.** Everything else, such as `l : list A`. When an argument in a data position has an
  instantiated type that is a function, the translation rejects it with `E_CLOSURE_DATA`,
  because the callee's time function has no companion for it.

### Time types

- `τ⟦Π(x:A).B⟧ = Π(x:A). [Π(T_x : τ⟦A⟧).] τ⟦B⟧`, where the bracketed binder is present exactly
  when `x` has a function shape.
- `τ⟦B⟧ = N` otherwise.

For example, the time type of `(A -> B) -> list A -> list B` is
`(A -> B) -> (A -> N) -> list A -> N`.

### The top-level rule

`TimeFun f` takes `f := λ params. [fix F args {struct i}] body` and produces:

```text
T_f := λ params⁺. [fix T_F args⁺ {struct i⁺}] 1 + T⟦body[F := f params]⟧
```

- `⁺` inserts a companion `T_x` after each binder with a function shape.
- `i⁺` shifts the structural index by the number of companions before position `i`.
- A use of the recursive variable as a value becomes the constant applied to its parameters,
  so that `T_rev` mentions `rev l'` and no bound fix variable.
- A call of the constant in head position becomes a call of `T_F`, with the parameters and
  their companions dropped.
- For a mutual block, every member that is a constant gets its own time function, each one a
  projection of the same translated block. A member is found by the name of its fix binder in
  the module of `f`. A member that is not a constant is replaced by the closed fix term.
- When the body returns a function, the time function is eta-expanded to the full arity of the
  type: `T_f params x̄⁺ = 1 + C⟦body⟧ + F⟦body⟧ x̄⁺`. This is exact for full applications. A
  partial application of `f` that a program reuses pays `1 + C⟦body⟧` at every call.

### Term rules

| Form | Cost |
| --- | --- |
| Bound variable, sort, product, primitive literal | 0 |
| Constant applied only to irrelevant arguments, with a result that is not a function | 0, because extraction evaluates it once, at start-up |
| `h a₁…aₙ` | `Σ_{data} T⟦aᵢ⟧ + Σ_{function} C⟦aᵢ⟧ + CALL(h, a⁺)`, where `a⁺` puts `F⟦aᵢ⟧` after each function argument. Nested applications are flattened first. |
| `CALL(K, _)` for a constructor | 0. A function argument gives `E_CLOSURE_DATA`. |
| `CALL(f, a⁺)` for the fix under translation | `T_F (drop params a⁺)` |
| `CALL(f, a⁺)` for a constant with a time function | `T_f a⁺` |
| `CALL(g, a⁺)` for a local function with a companion | `T_g a⁺` |
| `CALL(c, a⁺)` for a `TimePrim` constant | the declared cost, applied to `a⁺` |
| `CALL(c, a⁺)` for a local `fix` or mutual `fix` | the local time function, translated by the top-level rule, with the closed fix term as the value of its variables |
| `CALL` otherwise | `E_NO_TIME`, or `E_OPAQUE`, `E_SECTION` or `E_WF` when the callee is opaque, a section variable or a well-founded recursor |
| More arguments than the generic type of the callee has binders | `E_OVERAPP` |
| A partial application in a data position | `E_CLOSURE` |
| Primitive projection `s.(p)` | `T⟦s⟧`. A call of a projected function gives `E_NO_TIME`. |
| `let x := v in b`, `x` data | `T⟦v⟧ + let x := v in T⟦b⟧`, with the `let` dropped when `T⟦b⟧` doesn't use `x` |
| `let g := v in b`, `g` a function | `C⟦v⟧ + let g := v in let T_g := F⟦v⟧ in T⟦b⟧` |
| `(λx. k) m` | `let x := m in k`. A variable, a closure or an irrelevant argument is substituted, since evaluating it costs nothing. |
| A call of a `TimeUnfold` constant `c` | the body of `c` applied to the arguments, translated by the redex rule |
| `match e as y in I idx return P with pᵢ ⇒ bᵢ end` | `T⟦e⟧ + match e as y in I idx return N with pᵢ ⇒ T⟦bᵢ⟧ end`, folded to `T⟦e⟧` when every branch costs 0. A scrutinee in `Prop` costs 0. |
| `(match e return Π ȳ. P with p ⇒ λȳ. b end) prfs`, all `prfs` irrelevant | `T⟦e⟧ + (match e return Π ȳ. N with p ⇒ λȳ. T⟦b⟧ end) prfs` |
| A `match` that returns a function and is applied to data | `E_MATCH_FN` |
| `fun` or an unapplied `fix` in a data position | `E_CLOSURE` |
| Any other form | `E_TERM`. rocq-elpi can't read `cofix`, so a definition that contains one fails before translation. |

The rule for a `match` applied to proofs covers convoy matches, such as the one in
`examples/Halving.v`, whose branches take an equation as an argument.

### Function values

`F⟦e⟧` for `e : Π x̄. B` is eta-expanded over the binders of the slot that receives `e`.

- A local function with a companion has `F⟦g⟧ = T_g`.
- A closure has `F⟦λx̄. b⟧ = λ x̄⁺. 1 + T⟦b⟧` and `C⟦λx̄. b⟧ = 0`. The 1 per call makes every
  execution of a body cost at least 1.
- A partial application has `F⟦h ā⟧ = λ x̄⁺. CALL(h, (ā ++ x̄)⁺)` and `C⟦h ā⟧ = Σ T⟦ā⟧`, so the
  arguments are paid once, when the closure is created.
- A constructor used as a function has `F⟦K ā⟧ = λ x̄⁺. 1`.

### Names and lookup

- `T_<id>` lives in the same module as its constant. Companions are named `T_<binder>`.
- The time function of a constant of another library lives in a module named like the last
  component of the constant's path. So `Nat.add` gets `Argent.Std.Nat.T_add`, and `List.rev`
  gets `Argent.Std.List.T_rev`. `TimeFun` checks this, and reports `E_PLACE` otherwise.
- Lookup tries the database entry of the constant first. Then it tries the *sibling rule*,
  which resolves `<suffix>.T_<id>` for every suffix of the constant's path, from the longest to
  the shortest, and accepts only a hit whose own path matches the constant's path. The sibling
  rule finds the time functions of functor parameters and of functor instances, because
  database facts recorded inside a functor are dropped when the functor ends. Lookup tries the
  `TimePrim` table last.
- A time function found by the sibling rule that has a body is checked before it is used. The
  translator derives the time function of the callee again, which checks the callee's own
  callees in the same way, and requires the result to be convertible with the stored one. It
  reports `E_CHECK` otherwise. A sibling without a body, a `Parameter` of a module type, is used
  as it is. A callee whose body is another constant, as in a module alias, is checked through
  that constant. Each check runs once per command, and is recorded in the database.
- `T_f` copies the implicit arguments of `f`, with every companion explicit, and it is universe
  polymorphic exactly when `f` is.
- A definition that uses a section variable is rejected with `E_SECTION`, because its arity
  changes when the section closes.
- Every time function is declared `simpl never`, so that `cbn` and `simpl` leave it folded. The
  tactic `time_unfold` unfolds it by one step and folds its recursive calls back.

## 3. Where the code lives

| Part of the design | File |
| --- | --- |
| The translator (section 2), the databases and the commands, and `time_unfold` | `theories/Time.v` |
| The tactics that prove bounds | `theories/Tactics.v` |
| Time functions and bounds of the standard library, and the potential lemmas of `Fix_F`, `Fix`, `Acc_rect` and `well_founded_induction_type` | `theories/Std.v` |
| The complexity bounds and their notation | `theories/Complexity.v` |
| The potential method for sequences of operations [12] | `theories/Amortised.v` |
| The loop combinators and their potential lemmas | `theories/Loop.v` |
| Derivation, rejections, functors, tactics, the bounds of `Std`, the notation, well-founded recursion, large inputs, assumptions and extraction | `tests/Tests*.v`, one file per topic |

Some choices inside the library are worth recording:

- **Complexity bounds.** A bound quantifies over the tuple of all inputs, so its constant is
  uniform over all of them, as Guéneau and others recommend [9]. The lower bound is the upper
  bound with the time and the measure swapped, so each closure lemma of `bigO` gives its mirror
  in one line. `tight` is the upper bound together with the worst-case lower bound.

  ```coq
  Definition bigO {X} (P : X -> Prop) (g T : X -> N) : Prop :=
    exists c, forall x, P x -> T x <= c * (g x + 1).
  Definition tight {X} (P : X -> Prop) (g T : X -> N) : Prop :=
    bigO P g T /\ exists c, forall n, exists x, P x /\ n <= g x /\ g x <= c * T x.
  Definition bigOmega {X} (P : X -> Prop) (g T : X -> N) : Prop := bigO P T g.
  Definition bigTheta {X} (P : X -> Prop) (g T : X -> N) : Prop :=
    bigO P g T /\ bigOmega P g T.
  Definition bigOmega_worst {X} (P : X -> Prop) (g T : X -> N) : Prop :=
    exists c, forall n, exists x, P x /\ n <= g x /\ g x <= c * T x.
  Definition bigO_amortised {X} (P : X -> Prop) (g T before after : X -> N) : Prop :=
    exists c, forall x, P x -> T x + after x <= c * (g x + 1) + before x.
  ```

- **Preconditions stay predicates.** A subset type, or a record of well-formed inputs, would
  change every proof that takes a bound apart. `bigO_subset` gives the bound on the subset type
  `{x | P x}` for a reader who wants the domain as a type.
- **The letter 𝑂.** The notation writes the upper bound with the italic `𝑂` (U+1D442). With the
  ASCII letter, the lexer would read `O(` as one token, and the constructor `O` of `nat`
  followed directly by a comment, as in `S O(* ... *)`, would no longer parse.
- **Loops that compute.** `loop` recurses structurally on an accessibility proof, and
  `loop_fuel` takes `nat` fuel. An entry point builds the accessibility proof with
  `Acc_intro_generator`, so that the loop runs under `vm_compute`.

## 4. Meta-theory

The cost model is call-by-value evaluation of the extracted program, which is OCaml evaluation
without inlining. Types and proofs are erased. Constants applied only to irrelevant arguments
are evaluated once. Constants that extraction realises natively cost what `TimePrim` declares.
Everything else is Gallina code, so `positive` arithmetic costs one step per bit unless it is
realised natively.

**Claim.** For a closed call `f v̄`, let `M` be the number of steps of a call-by-value machine,
and `K` the size of the largest body reachable from `f`. Then `T_f v̄ <= M <= K * (T_f v̄ + 1)`.

**Argument.**

1. `T_f` adds exactly 1 per call of a defined function, or of a closure body that is passed to
   another function. The cost is a sum, so the order of evaluation doesn't matter. The cost is
   exact on `match`, which charges only the branch taken, and on `let`, which charges its value
   once.
2. Between two consecutive counted calls, the machine runs part of one body. A body has no loop
   other than calls, and each subterm runs at most once per execution of its body, so that part
   takes at most `K` steps. A closure that a redex substitutes, or that `TimeUnfold` inlines, is
   called at most once per execution of the enclosing body, so the same argument covers it
   without its own 1.
3. Hence `T_f v̄ <= M <= K * (T_f v̄ + 1)`, which is Θ.

The claim is argued here. It is not a theorem of the library.

**Companions.** A theorem quantifies over a companion `T_g` under hypotheses such as
`forall a, T_g a <= k`. At every call site the companion is `F⟦arg⟧`, derived from the
argument's own body, so instantiating the theorem is faithful.

**Trusted base.** The trusted parts are the Rocq kernel, the Elpi translator, the `TimePrim`
table and the extraction realisations of its entries. The translator is unverified, so a bug
in it could under-charge. `TimeCheck` makes sure that a stored time function equals what the
translator produces. It doesn't check the translator.

**A sharper check.** A project can extract with `Unset Extraction AutoInline`, profile function
entries with `ocamlfind ocamlcp -P f`, and compare the entry counts on fixtures with `T_f`
evaluated by `vm_compute`. Without native realisations, the counts should agree up to the
closures that the translation inlines. A formal proof of soundness would need a reflected
syntax, which MetaRocq provides. MetaRocq is not packaged for Rocq 9.3.

**Persistence and amortisation.** Worst-case contracts hold for every version of a data
structure. Amortised contracts are inequalities per operation on arbitrary states, so
`amortised_run` bounds any single sequence of versions. Nothing is claimed for a history in
which one version is used twice, because repeating an expensive operation on the same version
is the counterexample. Okasaki's laziness-based persistence [10] doesn't apply, because the
code is strict.

## 5. Enforcement

The commands give a project the following checks.

- Run `TimeAudit` on the roots of every extracted program. It walks the bodies reachable from
  the roots, fails on every computational constant that has neither a time function nor a
  `TimePrim` cost, and runs `TimeCheck` on every time function that it meets.
- Reject hand-written time functions with a lexical lint on the sources: a definition whose
  name starts with `T_` is an error, except a `Parameter T_` in a module type.
- Allow `TimePrim` in one reviewed file only.
- Require every operation of a module type to declare its time function and at least one
  contract `T_op_le`.
- Reject exact costs, such as `T_f x = 7`, in published theorems, so that statements don't
  change when a constant changes.
- Keep clients to the contracts of a signature, by rejecting `unfold M.T_op` outside the module
  that defines `T_op`.

rocq-elpi gives no access to the extraction tables, so no command reads the constants that
extraction realises natively. `TimePrimTable c …` fails unless the constants with a `TimePrim`
cost are exactly `c …`. So a project runs it on the constants of its `Extract Constant`
directives, and the test fails when a cost is declared or removed without the matching
directive. Argent ships no lint.

## 6. Limits

- Well-founded recursion works through `Fix`, `Fix_F`, `Acc_rect` and
  `well_founded_induction_type`, for a result type that is not a function. `Program Fixpoint`
  and `Function` are rejected, so such definitions must be rewritten with `Fix`, `loop` or
  `loop_fuel`. Equations is untested. The potential lemmas of the recursors quantify over every
  recursive-call function, so they don't bound a step whose cost depends on the results of its
  recursive calls.
- Closures can't be stored in data. Records of functions become functor parameters, and
  continuations stored in data must be defunctionalised [11].
- `cofix` is not supported.
- The translator is trusted. `TimeCheck` and the profile comparison of section 4 mitigate
  this.
- Elpi database facts recorded inside a functor are dropped when the functor ends. So lookups
  of time functions inside functors rely on the sibling rule, which checks every sibling with a
  body by deriving it again. rocq-elpi gives no way to tell that a command runs inside a
  functor, so the registration commands can't reject a run there.
- The guard checker accepts the derived time functions of the nested recursion that we tested:
  a tree whose constructor holds a `list` of subtrees, traversed either with `List.map` of the
  outer function or with a local `fix` over the list. Other nestings are untested.
- Binary arithmetic on `positive`, `N` and `Z` costs one step per bit. A project that realises
  it natively must declare its costs with `TimePrim`.

## 7. Literature

1. Nipkow, Eberl and Haslbeck (eds.), *Functional Data Structures and Algorithms: A Proof
   Assistant Approach*, ACM Books, 2025, §1.5. The Isabelle command `HOL-Library.Time_Commands`
   by J. Stahl is documented in
   [Time_Manual](https://isabelle.in.tum.de/library/HOL/HOL-Library/Time_Manual.html). Its
   zero-time primitives include polymorphic equality, which Argent avoids.
2. McCarthy, Fetscher, New, Feltey and Findler, "A Coq library for internal verification of
   running-times", FLOPS 2016 and SCP 2018.
3. Forster and Kunze, ITP 2019. Forster, Kunze and Roth, POPL 2020.
4. Charguéraud and Pottier, ITP 2015 and JAR 2019.
5. Mével, Jourdan and Pottier, ESOP 2019.
6. Niu, Sterling, Grodin and Harper, "A cost-aware logical framework", POPL 2022.
7. Handley, Vazou and Hutton, "Liquidate your assets", POPL 2020.
8. Hofmann and Jost, POPL 2003. Hoffmann and others, RaML.
9. Guéneau, Charguéraud and Pottier, "A Fistful of Dollars", ESOP 2018.
10. Okasaki, *Purely Functional Data Structures*, 1998.
11. Reynolds, 1972. Danvy and Nielsen, "Defunctionalization at work", PPDP 2001.
12. Nipkow, "Amortized Complexity Verified", ITP 2015. Nipkow and Brinkop, JAR 2019. Tarjan,
    "Amortized computational complexity", 1985.
13. Tassi, "Elpi: an extension language for Coq", CoqPL 2018.
14. Xia and others, demand semantics, ICFP 2024.
