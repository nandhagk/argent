# Argent design note

This note records why Argent derives time functions from plain Gallina, the translation that it
implements, what the library contains, why the derived costs are faithful, how a project can
enforce their use, and what the design cannot do.

## 1. Decision

Argent follows the time-function method of Nipkow and others [1], ported to Rocq with
rocq-elpi. Programs are plain Gallina. For each executable definition `f`, an Elpi command
defines a separate, transparent, `nat`-valued constant `T_f` from the kernel term of `f`. A
generic component is a functor whose signature carries a time layer next to its functional
layer.

The method meets the following requirements.

- Charges cannot be misplaced, because `T_f` is a function of the body of `f`. A changed charge
  needs a changed program. `TimeCheck` re-derives a stored time function, and `TimeAudit`
  checks that every executable constant reachable from a root has one.
- Published theorems are `bigO` statements, and internal lemmas use named constants.
- `T_f` counts call-by-value work up to a constant factor (section 4), so a bound that is
  proved tight is tight for the extracted program. Loop bounds are paid by a potential, so they
  do not depend on fuel or on an accessibility proof.
- Amortised bounds use one per-operation potential inequality, one sequence lemma and one loop
  lemma.
- Derivation is automatic, and the tactic `time_step` closes most per-operation bounds in one
  line.
- Module parameters work. A call `M.op` uses `M.T_op`, which the signature declares.
- The only dependency is rocq-elpi. Signature contracts are `Parameter`s of module types, which
  every instance proves, so no axiom is added.
- Code contains no accounting, so tests and extraction are unchanged. The accessibility loop
  extracts to `let rec loop step s = match step s with Inl s0 -> loop step s0 | Inr r -> r`.

The alternatives that we considered lose some of these properties.

| Alternative | What it loses |
| --- | --- |
| A writer monad that counts ticks, with charges placed by hand | Every function has a costed twin and an equation relating the two, and a lint must check where the charges are. Value proofs see the monad. |
| A monad whose cost lives in a `Prop` index [2] | Programs stay monadic and charges are placed by hand. |
| A functor over an abstract monad, instantiated at the identity and at a counter | Code stays monadic, and Rocq has no parametricity theorem to relate the two instances. |
| A translator in Ltac2 | Ltac2 has no command API and no persistent database, and building `match` and `fix` terms is fragile. Elpi binds variables in higher-order abstract syntax and is packaged. |
| Certifying extraction to the weak call-by-value λ-calculus L [3] | Its cost model is reasonable only up to a polynomial, so it is not tight for data structures. |
| Time credits in CFML or Iris [4, 5] | They verify OCaml or HeapLang programs. They do not verify Gallina. |
| Calf, Liquid Haskell `RTick`, RaML [6, 7, 8] | They need another proof assistant, ticks placed by hand, or an uncertified analysis. |

## 2. The translation

`T⟦e⟧ : nat` is the cost of call-by-value evaluation of `e`. `F⟦e⟧` is the time function of a
function-valued `e`, and `C⟦e⟧` is the cost of creating the closure `e`.

### Shapes

Every binder and argument position of type `D` has a shape. Shapes are computed on the generic
type of the callee, under its earlier binders, so that they agree with the type of the
callee's time function.

- **Irrelevant**: `D` is an arity (it ends in a sort), or `D` lives in `Prop` or `SProp`. Types,
  proofs and predicates are copied verbatim, cost 0 and get no companion.
- **Function**: the weak head normal form of `D` is a product, and `D` is not irrelevant. The
  argument gets a companion time function right after it, and the shape records the shapes of
  the binders of `D`.
- **Data**: everything else. When an argument in a data position has an instantiated type that
  is a function, the translation rejects it with `E_CLOSURE_DATA`, because the callee's time
  function has no companion for it.

### Time types

- `τ⟦Π(x:A).B⟧ = Π(x:A). [Π(T_x : τ⟦A⟧).] τ⟦B⟧`, where the bracketed binder is present iff `x`
  has a function shape.
- `τ⟦B⟧ = nat` otherwise.

### The top-level rule

`TimeFun f` takes `f := λ params. [fix F args {struct i}] body` and produces the following.

```
T_f := λ params⁺. [fix T_F args⁺ {struct i⁺}] 1 + T⟦body[F := f params]⟧
```

- `⁺` inserts a companion `T_x` after each binder with a function shape.
- `i⁺` shifts the structural index by the number of companions before position `i`.
- Value occurrences of the recursive variable become the constant applied to its parameters,
  so that `T_rev` mentions `rev l'` and no bound fix variable.
- Calls of the constant in head position become calls of `T_F`, with the parameters and their
  companions dropped.
- For a mutual block, every member that is a constant gets its own time function, each one a
  projection of the same translated block. A member is found by the name of its fix binder in
  the module of `f`. A member that is not a constant is replaced by the closed fix term.
- When the body returns a function, the time function is eta-expanded to the full arity of the
  type: `T_f params x̄⁺ = 1 + C⟦body⟧ + F⟦body⟧ x̄⁺`. This is exact for full applications. A
  reused partial application of `f` pays `1 + C⟦body⟧` at every call.

### Term rules

| Form | Rule |
| --- | --- |
| Bound variable, sort, product, primitive literal | 0 |
| Constant applied only to irrelevant arguments, with a result that is not a function | 0, because extraction evaluates it once at start-up. |
| `h a₁…aₙ` | `Σ_{data} T⟦aᵢ⟧ + Σ_{function} C⟦aᵢ⟧ + CALL(h, a⁺)`, where `a⁺` places `F⟦aᵢ⟧` after each function argument. Nested applications are flattened first. |
| `CALL(K, _)` for a constructor | 0. A function argument gives `E_CLOSURE_DATA`. |
| `CALL(f, a⁺)` for the fix under translation | `T_F (drop params a⁺)` |
| `CALL(f, a⁺)` for a constant with a time function | `T_f a⁺` |
| `CALL(g, a⁺)` for a local function with a companion | `T_g a⁺` |
| `CALL(c, a⁺)` for a `TimePrim` constant | the declared cost applied to `a⁺` |
| `CALL(c, a⁺)` for a local `fix` or mutual `fix` | the local time function, translated by the top-level rule with the closed fix term as the value of its variables |
| `CALL` otherwise | `E_NO_TIME`, or `E_OPAQUE`, `E_SECTION` or `E_WF` when the callee is opaque, a section variable or a well-founded recursor |
| More arguments than the generic type of the callee has binders | `E_OVERAPP` |
| A partial application in a data position | `E_CLOSURE` |
| Primitive projection `s.(p)` | `T⟦s⟧`. A call of a projected function gives `E_NO_TIME`. |
| `let x := v in b`, `x` data | `T⟦v⟧ + let x := v in T⟦b⟧`, with the `let` dropped when `T⟦b⟧` does not use `x` |
| `let g := v in b`, `g` a function | `C⟦v⟧ + let g := v in let T_g := F⟦v⟧ in T⟦b⟧` |
| `(λx. k) m` | `let x := m in k`. A variable, a closure or an irrelevant argument is substituted, since evaluating it costs nothing. |
| A call of a `TimeUnfold` constant `c` | the body of `c` applied to the arguments, translated by the redex rule |
| `match e as y in I idx return P with pᵢ ⇒ bᵢ end` | `T⟦e⟧ + match e as y in I idx return nat with pᵢ ⇒ T⟦bᵢ⟧ end`, folded to `T⟦e⟧` when every branch costs 0. A scrutinee in `Prop` costs 0. |
| `(match e return Π ȳ. P with p ⇒ λȳ. b end) prfs`, all `prfs` irrelevant | `T⟦e⟧ + (match e return Π ȳ. nat with p ⇒ λȳ. T⟦b⟧ end) prfs` |
| A `match` that returns a function and is applied to data | `E_MATCH_FN` |
| `fun` or an unapplied `fix` in a data position | `E_CLOSURE` |
| Any other form | `E_TERM`. rocq-elpi cannot read `cofix`, so a definition that contains one fails before translation. |

### Function values

`F⟦e⟧` for `e : Π x̄. B` is eta-expanded over the binders of the slot that receives `e`.

- A local function with a companion has `F⟦g⟧ = T_g`.
- A closure has `F⟦λx̄. b⟧ = λ x̄⁺. 1 + T⟦b⟧` and `C⟦λx̄. b⟧ = 0`. The 1 per invocation makes every
  body execution cost at least 1.
- A partial application has `F⟦h ā⟧ = λ x̄⁺. CALL(h, (ā ++ x̄)⁺)` and `C⟦h ā⟧ = Σ T⟦ā⟧`, so the
  arguments are paid once, when the closure is created.
- A constructor used as a function has `F⟦K ā⟧ = λ x̄⁺. 1`.

### Names and lookup

- `T_<id>` lives in the same module as its constant. Companions are named `T_<binder>`.
- The time function of a constant of another library lives in a module named like the last
  component of the constant's path. So `Nat.add` gets `Argent.Std.Nat.T_add` and `List.rev`
  gets `Argent.Std.List.T_rev`. `TimeFun` checks this and reports `E_PLACE` otherwise.
- Lookup tries the database entry of the constant first. It then tries the sibling rule, which
  resolves `<suffix>.T_<id>` for every suffix of the constant's path, from longest to shortest,
  and accepts only a hit whose own path equals the constant's path. The sibling rule finds the
  time functions of functor parameters and of functor instances, where Elpi databases cannot be
  extended. Lookup tries the `TimePrim` table last.
- A time function found by the sibling rule that has a body is checked before it is used. The
  translator derives the time function of the callee again, which checks the callee's own
  callees in the same way, and requires the result to be convertible with the stored one. It
  reports `E_CHECK` otherwise. A sibling without a body, a `Parameter` of a module type, is used
  as it is. A callee whose body is another constant, as in a module alias, is checked through
  that constant. Each check runs once per command and is recorded in the database.
- `T_f` copies the implicit status of `f`, with every companion explicit, and is universe
  polymorphic iff `f` is.
- A definition that uses a section variable is rejected with `E_SECTION`, because its arity
  changes when the section closes.
- Every time function is declared `simpl never`, so that `cbn` and `simpl` leave it folded. The
  tactic `time_unfold` unfolds it by one step and refolds its recursive calls.

## 3. The library

The library has six theories.

- `Time` holds the translator and the commands. `TimeFun` derives time functions. `TimeCheck`
  re-derives and compares. `TimeAudit` walks the constants reachable from roots. `TimePrim`
  declares a built-in cost and is the only way to write one. `TimeUnfold` marks a constant to
  unfold before translation. `TimeBound` registers a bound for `time_pose`.
- `BigO` defines the following, where `X` is the tuple of all inputs, so the constant is
  uniform over all of them, as Guéneau and others recommend [9].

  ```coq
  Definition bigO {X} (P : X -> Prop) (g T : X -> nat) : Prop :=
    exists c, forall x, P x -> T x <= c * (g x + 1).
  Definition tight {X} (P : X -> Prop) (g T : X -> nat) : Prop :=
    bigO P g T /\ exists c, forall n, exists x, P x /\ n <= g x /\ g x <= c * T x.
  ```

- `Amortised` proves `amortised_run` and `amortised_uniform` for a sequence of operations
  `op : O -> S -> S`, a potential `Phi` and an invariant `Inv` [12].
- `Loop` defines `loop`, which recurses structurally on an accessibility proof, and
  `loop_fuel`, which takes `nat` fuel. Their potential lemmas `T_loop_le` and `T_loop_fuel_le`
  bound the time by `Phi s + Tstop + 1` when every continuing step pays its cost and its call
  from a strict decrease of `Phi`. An entry point builds the proof with
  `Acc_intro_generator`, so the loop runs under `vm_compute`.
- `Std` derives the time functions of the standard library's functions on lists, booleans,
  pairs, `nat`, `positive`, `N` and `Z`, with bounds in the length of a list or the bit length
  of a number.
- `Tactics` holds `time_pose`, `time_simpl`, `time_step`, `loop_bound` and `amortise`.

## 4. Meta-theory

The cost model is call-by-value evaluation of the extracted program, which is OCaml
evaluation without inlining. Types and proofs are erased. Constants applied only to irrelevant
arguments are evaluated once. Constants realised natively by extraction cost what `TimePrim`
declares. Everything else is Gallina code, so `positive` arithmetic costs one step per bit
unless it is realised natively.

**Claim.** For a closed call `f v̄`, let `N` be the number of steps of a call-by-value machine and
`K` the size of the largest body reachable from `f`. Then `T_f v̄ <= N <= K * (T_f v̄ + 1)`.

**Argument.**

1. `T_f` adds exactly 1 per invocation of a defined function or of a closure body that is
   passed to another function. The cost is a sum, so the order of evaluation does not matter.
   The cost is exact on `match`, which charges only the branch taken, and on `let`, which
   charges its value once.
2. Between two consecutive counted invocations, the machine runs part of one body. A body has
   no loop other than calls, and each subterm runs at most once per execution of its body, so
   that part takes at most `K` steps. A closure that a redex substitutes or that `TimeUnfold`
   inlines is called at most once per execution of the enclosing body, so the same argument
   covers it without its own 1.
3. Hence `T_f v̄ <= N <= K * (T_f v̄ + 1)`, which is Θ.

The claim is argued here and is not a theorem of the library.

**Companions.** A theorem quantifies over a companion `T_g` under hypotheses such as
`forall a, T_g a <= k`. At every call site the companion is `F⟦arg⟧`, derived from the
argument's own body, so instantiating the theorem is faithful.

**Trusted base.** The trusted parts are the Rocq kernel, the Elpi translator, the `TimePrim`
table and the extraction realisations of its entries. The translator is unverified, so a bug in
it could under-charge. `TimeCheck` makes a stored time function equal to what the translator
produces, and it does not check the translator.

**A sharper check.** A project can extract with `Unset Extraction AutoInline`, profile function
entries with `ocamlfind ocamlcp -P f`, and compare the entry counts on fixtures with `T_f`
evaluated by `vm_compute`. Without native realisations the counts should agree up to the
closures that the translation inlines. A formal soundness proof would need a reflected
syntax, which MetaRocq provides. MetaRocq is not packaged for Rocq 9.3.

**Persistence and amortisation.** Worst-case contracts hold for every version. Amortised
contracts are per-operation inequalities on arbitrary states, so `amortised_run` bounds any
single sequence of versions. Nothing is claimed for a history in which one version is used
twice, because repeating an expensive operation on the same version is the counterexample.
Okasaki's laziness-based persistence [10] does not apply, because the code is strict.

## 5. Enforcement

The commands give a project the following checks.

- Run `TimeAudit` on the roots of every extracted program. It walks the bodies reachable from
  the roots transitively, fails on every computational constant that has neither a time
  function nor a `TimePrim` cost, and runs `TimeCheck` on every time function that it meets.
- Reject hand-written time functions with a lexical lint on the sources. A definition whose name
  starts with `T_` is a lint error, except a `Parameter T_` in a module type.
- Allow `TimePrim` in one reviewed file only.
- Require every operation of a module type to declare its time function and at least one
  contract `T_op_le`.
- Reject exact costs, such as `T_f x = 7`, in published theorems, so that statements do not
  change when a constant changes.
- Keep clients to the contracts of a signature, by rejecting `unfold M.T_op` outside the module
  that defines `T_op`.

rocq-elpi gives no access to the extraction tables, so no command reads the constants that
extraction realises natively. `TimePrimTable c …` fails unless the constants with a `TimePrim`
cost are exactly `c …`, so a project runs it on the constants of its `Extract Constant`
directives, and the test fails when a cost is declared or removed without the matching
directive. Argent ships no lint.

## 6. Limits

- Well-founded recursion by `Fix`, `Program Fixpoint`, `Function` or Equations is rejected, so
  such definitions must be rewritten with `loop` or `loop_fuel`.
- Closures cannot be stored in data. Records of functions become functor parameters, and
  continuations stored in data must be defunctionalised [11].
- `cofix` is not supported.
- The translator is trusted. `TimeCheck` and the profile comparison of section 4 mitigate this.
- Elpi database facts recorded inside a functor are dropped when the functor ends, so lookups
  of time functions inside functors rely on the sibling rule.
- The guard checker accepts the derived time functions of the nested recursion that we tested.
  The tested type is a tree whose constructor holds a `list` of subtrees, traversed either with
  `List.map` of the outer function or with a local `fix` over the list. Other nestings are
  untested.
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
