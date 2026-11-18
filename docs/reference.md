# Argent reference

This page describes the cost model, every command and tactic, the complexity bounds and their
lemmas, and every error code. [The tutorial](tutorial.md) introduces the same things through
examples, one at a time.

- [Cost model](#cost-model)
- [Commands](#commands)
- [Tactics](#tactics)
- [Complexity bounds](#complexity-bounds)
- [Sizes and scopes](#sizes-and-scopes)
- [Signatures with a time layer](#signatures-with-a-time-layer)
- [Amortised bounds, loops and well-founded recursion](#amortised-bounds-loops-and-well-founded-recursion)
- [Error codes](#error-codes)
- [Limits](#limits)

## Cost model

`T_f a1 … an` is the number of steps that the call `f a1 … an` takes under call-by-value
evaluation of the extracted program. A step is one call of a defined function, or one call of
the body of a closure. Each kind of term costs the following.

| Term | Cost | Example |
| --- | --- | --- |
| A call `g a1 … an` | the costs of evaluating the arguments, plus `T_g a1 … an` | `append r l2` costs `T_append r l2`, because `r` and `l2` are variables |
| The body of `f` | 1 for the call of `f`, plus the cost of the body | `T_append [] l2 = 1` |
| `match e with … end` | the cost of `e`, plus the cost of the branch that runs | `T_pop` pays for the reversal only in the branch where the front list is empty |
| `let x := v in b` | the cost of `v`, once, plus the cost of `b` | |
| A constructor `K a1 … an` | the costs of its arguments only | `x :: append r l2` costs `T_append r l2` |
| A variable or a literal | 0 | |
| A type or a proof | 0, because extraction erases it | the proof `div2_lt x q E` in `examples/Halving.v` |
| A constant applied only to types and proofs, such as `@nil A` | 0, because the extracted program evaluates it once, at start-up | |

A function argument `g` of `f` gets a *companion* `T_g`, its time function, right after it in
`T_f`. So `T_map` has the type
`forall {A B : Type}, (A -> B) -> (A -> N) -> list A -> N`. At a call site, `TimeFun` derives
the companion from the argument itself:

| Argument | Companion | Cost of creating it |
| --- | --- | --- |
| A closure `fun x => e` | `fun x => 1 + (the cost of e)` | 0 |
| A partial application `h a` | `fun x => T_h a x` | the cost of evaluating `a`, paid once, when the closure is created |
| A constructor used as a function, `K a` | `fun x => 1` | the cost of evaluating `a` |
| A local function with a companion | that companion | 0 |

Function values may be passed as arguments, and they may not be stored in data: a closure
taken out of a list or a record has no companion. See `E_CLOSURE_DATA` below.

What the model counts, and how exactly:

- **Steps up to a constant factor.** A body contains no loop other than calls, so the work
  between two counted calls is bounded by the size of the largest body. The real number of
  steps is between `T_f` and a constant times `T_f + 1`. [The design note](design.md)
  argues this. It is not a theorem of the library.
- **Numbers are the standard library's inductive types.** `nat` arithmetic is unary, and
  arithmetic on `positive`, `N` and `Z` costs one step per bit. A constant that extraction
  realises natively must declare its cost with [`TimePrim`](#timeprim).
- **Times are binary numbers of type `N`.** So `vm_compute` evaluates a time function quickly
  even on large inputs. `tests/TestsLarge.v` evaluates the time of `rev_append` on 1,000,000
  elements. Evaluating `T_f` can take longer than running `f`, because it also recomputes the
  values that the time functions of the callees receive. For example, `List.T_rev` computes
  `rev` of every suffix of its argument, so evaluating it takes time cubic in the length of
  the list, while `rev` itself takes quadratic time.
- **A function that returns a function is eta-expanded.** For example,
  `Pos.compare := Pos.compare_cont Eq` becomes a function of two arguments. A partial
  application that a program reuses then pays the cost of creating the closure at every call,
  so the model overestimates it by a constant per call.
- **A substituted closure isn't charged its call.** A closure that a beta-redex or `TimeUnfold`
  substitutes is not charged the 1 of its call, while a closure bound by `let` is. Both are
  within the constant factor.

## Commands

The commands are in `Argent.Time`, so a file that derives time functions starts with
`From Argent Require Import Time.`

### `TimeFun`

`TimeFun f g …` derives `T_f`, `T_g`, … and declares each one next to its constant.

```coq
TimeFun append.
```

- **Mutual definitions.** For a mutual block, `TimeFun` derives a time function for every
  member that is a constant, as one mutual fixpoint.
- **Constants of another library.** `TimeFun` must run in a module named like the last
  component of the constant's path, so that `Nat.add` gets `Nat.T_add`. `Argent.Std` already
  does this for the standard library.
- **How callees are charged.** A call of `g` is charged with the time function that an earlier
  `TimeFun` recorded for `g`. Failing that, it is charged with the constant `T_g` next to `g`,
  which is how `TimeFun` finds the time functions of functor parameters and instances (the
  *sibling rule*).
- **Hand-written time functions are caught.** When that `T_g` has a body, `TimeFun` first
  derives the time function of `g` again, and fails with `E_CHECK` unless the two are
  convertible. The check reaches the callees of `g` in turn, so a hand-written time function is
  caught at any depth. A `T_g` without a body, such as a `Parameter` of a module type, is used
  as it is. Each check runs once per command, and its result is kept for later commands, until
  the end of the enclosing functor if there is one.
- **Aliases.** A constant whose body is another constant, as in the module alias
  `Module K := K0.`, is charged with the time function of that constant, because extraction
  defines it as that constant.
- **What `T_f` looks like.** `T_f` has the implicit arguments of `f`, and every companion is
  explicit. `T_f` is universe polymorphic exactly when `f` is. It never unfolds under `cbn` or
  `simpl`. Unfold it with [`time_unfold`](#time_unfold) or [`time_step`](#time_step).

### `TimeCheck`

`TimeCheck f …` derives the time function of `f` again, and fails unless it is convertible
with the stored `T_f`. So a time function that was written or edited by hand is caught.

```coq
TimeCheck append.
```

### `TimeAudit`

`TimeAudit r …` visits every constant that the roots `r …` call, directly or not. It runs
`TimeCheck` on each one, and fails on a computational constant that has neither a time
function nor a `TimePrim` cost. Run it on the functions that you extract.

```coq
TimeAudit Trie.get Trie.set Trie.remove Queue.step.
```

### `TimePrim`

`TimePrim c := (e)` declares the cost `e` of a constant `c` that has no body to read, such as
an opaque constant or one that extraction replaces by native code. `e` has the time type of
`c`: the type of `c`, with `N` as the result and a companion after each function argument.
`TimePrim c := n` declares a constant cost `n`, which becomes a literal of type `N`. Put any
scope delimiter, such as `%N`, inside the parentheses, because the command doesn't read one
after them.

```coq
TimePrim opaque_double := (fun n => (N.of_nat n + 1)%N).
```

`TimePrim` is the only way to write a cost by hand, so its uses are the place to review.

### `TimePrimTable`

`TimePrimTable` prints every cost declared with `TimePrim`, sorted by the full name of the
constant. `TimePrimTable c …` also fails unless the constants with a declared cost are exactly
`c …`.

```coq
TimePrimTable opaque_double opaque_triple.
```

No command can read the extraction tables. So a project that realises constants natively runs
`TimePrimTable` in a test, on the constants of its `Extract Constant` directives. The test
fails when a cost is declared or removed without the matching directive.

### `TimeUnfold`

`TimeUnfold c …` makes the translation unfold `c` at every call, before translating the call.
A beta-redex `(fun x => k) m` that results is charged as `let x := m in k`. So code written in
an identity monad costs what the same code written with `let` costs.

```coq
Definition bind {A B : Type} (m : M A) (f : A -> M B) : M B := f m.
TimeUnfold ret bind.
```

`TimeUnfold` rejects a recursive constant. Inlining its fixpoint at every call would cost what
a call of its time function costs, and it would hide that time function from its bound.

### `TimeBound`

`TimeBound L` registers a lemma `L : forall xs, [P xs ->] (T_g args <= B)%N`, which
[`time_pose`](#time_pose) and `time_step` then use. A lemma named `T_g_le` next to `T_g` is
found without registration. Inside a functor, naming the lemma `T_g_le` is the only way,
because a registration made inside a functor is dropped when the functor ends.

```coq
Definition twice (n : nat) : nat := n + n.

TimeFun twice.

Lemma twice_bound (n : nat) : (T_twice n <= N.of_nat n + 2)%N.
Proof.
  time_step.
Qed.

TimeBound twice_bound.
```

### `TimeFunFails`

`TimeFunFails "E_CODE" f` succeeds when `TimeFun f` fails with the error code `E_CODE`, and it
declares nothing. It is meant for tests.

## Tactics

The tactics are in `Argent.Tactics`.

### `time_unfold`

`time_unfold @T_f` unfolds `T_f` by one step wherever its structural argument is a
constructor, and folds its recursive calls back.

```coq
time_unfold @T_rev_onto.
```

On the goal `T_rev_onto (x :: r) acc = …`, it leaves `1 + T_rev_onto r (x :: acc) = …`.

### `time_simpl`

`time_simpl` replaces each time function whose value is a number, such as `T_negb b` or
`T_count_step n`, by that number.

### `time_cbn`

`time_cbn` runs `cbn`, but keeps the arithmetic of `N` folded, so that `lia` can read the goal.
It computes specification functions such as `length (x :: l)`, and it rewrites `N.of_nat (S n)`
to `N.of_nat n + 1`. Time functions stay folded, as they always do. `time_cbn_all` does the
same in every hypothesis.

A plain `cbn` would turn `1 + t` into a `match` on `t`, and `N.of_nat (S n)` into a `positive`
literal over `Pos.of_succ_nat n`, which `lia` can't read. The folded constants are `N.add`,
`N.mul`, `N.sub`, `N.succ`, `N.pred`, `N.max`, `N.min`, `N.div`, `N.modulo`, `N.pow` and
`N.of_nat`. Size functions such as `N.size_nat`, and conversions such as `Z.abs_N` and
`N.to_nat`, still compute.

### `time_pose`

`time_pose` adds a hypothesis for each time function applied in the goal: its bound registered
with `TimeBound`, its sibling `T_g_le`, and the quantified hypotheses that match it, such as a
generalised induction hypothesis or a bound on a companion. It discharges the premises of
conditional bounds with `assumption`, `lia` or `eauto with time_inv`.

### `time_step`

`time_step` proves most bounds of the form `T_f args <= e` in one line. It unfolds the time
function on the left by one step, runs `time_simpl` and `time_cbn`, and poses the bounds with
`time_pose`. Then it tries `time_lin` and `nia`. When both fail, it destructs the scrutinees of
the matches left in the goal and tries again. `time_step f` unfolds the time function of `f`
instead.

```coq
induction l1 as [| x r IH]; time_step.
```

When `time_step` can't close the goal, it leaves it unfolded and simplified, with the bounds
posed, so you can see what remains.

### `time_lin`

`time_lin` closes a goal that is linear once each product with an abstract constant counts as
one variable, such as `c_map * (bits k + 1)`, where `c_map` is a `Parameter` of a signature.
It distributes the products, adds `c * a <= c * b` for each hypothesis `a <= b` on `N` and each
such constant `c` (and the same through `N.of_nat` for hypotheses on `nat`), replaces the
remaining products by fresh variables, and calls `lia`. It runs only when a constant multiplies
a term, and it fails with the goal unchanged. `time_step` calls it before `nia`.

### `loop_bound`

`loop_bound Inv Phi Tstop` applies [`T_loop_le`](#amortised-bounds-loops-and-well-founded-recursion)
or `T_loop_fuel_le` to a goal `T_loop … s H <= e` or `T_loop_fuel … s <= e`. It leaves the
premises of the lemma and, unless `lia` solves it, the arithmetic goal `Phi s + Tstop + 1 <= e`.

### `amortise`

`amortise Inv Phi A k` applies `amortised_uniform` to a goal `total op T os s <= e`. It leaves
four goals: `amortised op T A Phi Inv`, the cap `A o s <= k`, `Inv s`, and, unless `lia` solves
it, the arithmetic goal `k * N.of_nat (length os) + Phi s <= e`.

## Complexity bounds

`Argent.Complexity` defines the bounds. Each bound relates a time function `T` to a measure `g`
on the inputs `x` that satisfy a precondition `P`. The input is the tuple of all arguments, so
the constant of a bound doesn't depend on any of them.

| Bound | Constant | Meaning, for the inputs that satisfy `P` |
| --- | --- | --- |
| 𝑂 | `bigO P g T` | `T x <= c * (g x + 1)` for one constant `c` |
| Ω | `bigOmega P g T` | `g x <= c * (T x + 1)` for one constant `c` |
| Θ | `bigTheta P g T` | both of the above |
| Ω in the worst case | `bigOmega_worst P g T` | for every `n`, some input with `n <= g x` has `g x <= c * T x`, for one constant `c` |
| Θ in the worst case | `tight P g T` | 𝑂, and Ω in the worst case |
| amortised 𝑂 | `bigO_amortised P g T before after` | `T x + after x <= c * (g x + 1) + before x` for one constant `c` |

A lookup in a trie that misses can stop after one step, so its time has no lower bound in the
length of the key on every input. It has one in the worst case, because on a trie that holds
the key the lookup reads every bit. Ω in the worst case states that kind of bound. The
amortised bound counts the potential `before x` that an operation finds and the potential
`after x` that it leaves.

### Notation

`Import ComplexityNotations.` after `From Argent Require Import Complexity.` gives every bound
a notation:

| Notation | Constant |
| --- | --- |
| `T ∈ 𝑂(g) for x \| P` | `bigO` |
| `T ∈ Ω(g) for x \| P` | `bigOmega` |
| `T ∈ Θ(g) for x \| P` | `bigTheta` |
| `T ∈ Ω_worst(g) for x \| P` | `bigOmega_worst` |
| `T ∈ Θ_worst(g) for x \| P` | `tight` |
| `T ∈ 𝑂(g) amortised a ↦ b for x \| P` | `bigO_amortised`, with `before := a` and `after := b` |

```coq
Theorem get_complexity {A : Type} :
  T_get (A := A) p m ∈ 𝑂(N.of_nat (Pos.size_nat p)) for (p, m).
```

This statement is the term
`bigO (fun _ => True) (fun '(p, m) => N.of_nat (Pos.size_nat p)) (fun '(p, m) => T_get p m)`.

- **Binders.** `x` is a name or a tuple pattern without a quote, such as `(p, m)`. It binds the
  variables of the time, the measure, the precondition and the potentials. A pattern can't give
  types, so a statement names an implicit argument, as `(A := A)` above, when nothing else
  fixes it.
- **Preconditions.** Without `| P`, the precondition is `True`.
- **The letter 𝑂.** The upper bound is written with `𝑂` (U+1D442, mathematical italic capital
  O), a different character from the constructor `O` of `nat`. So a file that imports the
  notation keeps writing `O` as before. With the ASCII letter, `O(` would become one token, and
  a comment right after `O`, as in `S O(* … *)`, would no longer parse.
- **Levels.** A bound is at level 70 with no associativity, like `=` and `<=`. The time is read
  at level 69, so a sum of times needs no parentheses. The measure is read at level 200 inside
  its parentheses, and the potentials at level 69.
- **Where a precondition ends.** The precondition is read at level 200, so it extends to the end
  of the statement, like the body of `forall`. A bound with a precondition needs parentheses
  when more text follows it, such as `->` and a conclusion. A bound without one is a term of
  level 70, which `/\` and `->` join like an equation.
- **Scopes.** The time, the measure and the potentials are read in `N_scope`, and the
  precondition in the scope of the statement.
- **Printing.** Rocq prints every bound in the notation, also one written with `fst` and `snd`,
  and it breaks a long line before `for`.

### Lemmas

Prove a bound with explicit constants first, and state the complexity as a corollary of it.

| To | Use |
| --- | --- |
| Prove 𝑂 from a bound with a constant `c` | `bigO_intro` (`T x <= c * g x + c`) |
| Bound a smaller time, or use a larger measure | `bigO_le`, `bigO_mono` |
| Add two bounds, chain two bounds, or compose with a function on inputs | `bigO_add`, `bigO_trans`, `bigO_comp` |
| Do the same for lower bounds | `bigOmega_intro`, `bigOmega_le` (a larger time), `bigOmega_mono` (a smaller measure), `bigOmega_add`, `bigOmega_trans`, `bigOmega_comp` |
| Combine tight bounds | `bigTheta_intro`, `bigTheta_add`, `bigTheta_trans`, `bigTheta_comp`, `bigTheta_sym` |
| Prove Θ for a time that equals its measure plus a constant | `bigTheta_shift` |
| Prove a worst-case bound from inputs of every size | `tight_intro`, `bigOmega_worst_intro` |
| Turn Ω or Θ on every input into a worst-case bound | `bigOmega_worst_of_bigOmega`, `tight_of_bigTheta` |
| Split `tight` into 𝑂 and Ω in the worst case | `tight_iff` |
| Prove or convert an amortised bound | `bigO_amortised_intro`, `bigO_amortised_sub`, `bigO_amortised_of_bigO` |
| Bound a whole sequence of operations from an amortised bound | `bigO_amortised_run` |
| Restate a bound with a precondition as one on the subset type `{x \| P x}` | `bigO_subset` |

## Sizes and scopes

Every statement about time follows one rule. Time functions, time constants, potentials and
bounds have type `N`. A size that is a `nat`, such as `length l`, `Pos.size_nat p`,
`N.size_nat n` or the bit length of a `Z`, stays a function with values in `nat`, and it enters
a bound as `N.of_nat` of the size. A size that is already an `N`, such as the argument
`x : N` of a function that halves it, enters a bound as it is. A file of bounds can open
`N_scope` and mark its statements about sizes alone with `%nat`, as `Argent.Std` does.

## Signatures with a time layer

A module type that describes an operation has two layers. The functional layer declares the
operation and its laws. The time layer declares the time function, a named constant, and a
contract that bounds the time function by that constant.

```coq
Module Type MAP.
  Declare Module K : KEY.
  Parameter t : Type -> Type.
  Parameter get : forall {A : Type}, K.t -> t A -> option A.
  Parameter set : forall {A : Type}, K.t -> A -> t A -> t A.
  Parameter get_set_same : forall A k (v : A) m, get k (set k v m) = Some v.
  (* The time layer. *)
  Parameter T_get : forall {A : Type}, K.t -> t A -> N.
  Parameter c_map : N.
  Parameter T_get_le :
    forall A k (m : t A), (T_get k m <= c_map * (N.of_nat (Pos.size_nat (K.encode k)) + 1))%N.
End MAP.
```

An implementation defines the operation, runs `TimeFun` on it, which derives `T_get`, and
proves `T_get_le` for its own value of `c_map`. A client is a functor over the signature. Its
own `TimeFun` charges a call of `M.get` with `M.T_get` through the sibling rule, and its bounds
can use only the contracts, so they hold for every implementation. The contracts are
`Parameter`s of the module type, so they add no axiom: every instance must prove them.
`examples/KeyedMap.v` follows this pattern in full.

## Amortised bounds, loops and well-founded recursion

These lemmas all bound a cost with a potential `Phi`, a number attached to each state.

**Amortised bounds** (`Argent.Amortised`). Write the operations as one function
`step : op -> S -> S` over an inductive type `op` of operations, and run `TimeFun step`. Then:

1. Choose a potential `Phi : S -> N`, an invariant `Inv`, and an amortised cost `A o s : N`.
2. Prove `amortised step T_step A Phi Inv`: every operation keeps `Inv`, and
   `T_step o s + Phi (step o s) <= A o s + Phi s`.
3. Apply `amortised_run` for the exact statement on a sequence, or `amortised_uniform` (through
   the tactic `amortise`) for `total step T_step os s <= k * N.of_nat (length os) + Phi s`.

The bound holds along one sequence of versions. It says nothing about a history in which one
version is used twice, because repeating an expensive operation on the same version is not
paid for.

**Loops** (`Argent.Loop`). `loop lt step s H` runs `step` until it returns a result, and
recurses on the accessibility proof `H`. `loop_fuel step fuel s` runs it at most `fuel` times.
`T_loop_le` and `T_loop_fuel_le` say: if each step that continues keeps `Inv` and satisfies
`T_step s + Phi s1 < Phi s`, and each step that stops costs at most `Tstop`, then the loop from
`s` costs at most `Phi s + Tstop + 1`. The potential must drop by more than the step costs,
because each iteration also costs one call. The bounds hold for every proof and every amount of
fuel.

**Well-founded recursion** (`Argent.Std`, module `Wf`). `Std` derives the time functions of
`Fix_F`, `Fix`, `Acc_rect` and `well_founded_induction_type`, so a definition written with one
of them gets its time function from `TimeFun` like any other. The companion `T_F` of the
functional `F` takes the companion `T_rec` of its recursive-call argument. Each recursive call
costs `1 + T_Fix_F … y _`, where the 1 is the call of the closure that `Fix_F` passes to `F`.
`Wf.T_Fix_le` says that `T_Fix Rwf P F T_F x <= Phi x + 1` when every step satisfies
`T_F x rec T_rec + 1 <= Phi x`, for every `rec` and every `T_rec` with
`T_rec y h <= Phi y + 1`. `Wf.T_Fix_F_le`, `Wf.T_Acc_rect_le` and
`Wf.T_well_founded_induction_type_le` say the same for the other recursors.
`examples/Halving.v` uses `Wf.T_Fix_le`.

A `Fix` over a well-foundedness proof that ends in `Qed`, such as `N.lt_wf_0`, doesn't compute
under `vm_compute`, because the accessibility proof never reduces to a constructor. Wrapping the
proof in `Acc_intro_generator n`, which lazily adds `2 ^ n` constructors in front of it, makes
the function compute. Extraction erases the proof, so the extracted `log2` of
`examples/Halving.v` is `let rec log2 x = log2_step x (fun y _ -> log2 y)`.

## Error codes

`TimeFun` rejects a definition whose cost it can't account for. Each rejection has a code.

| Code | Cause | What to do |
| --- | --- | --- |
| `E_CLOSURE_DATA` | A function value is stored in a constructor, or passed where a polymorphic callee expects data. | Don't store functions in data. Make a record of functions a functor parameter, and defunctionalise continuations. |
| `E_CLOSURE` | A function value appears where data is expected. | Keep function values out of data positions, such as the result of a polymorphic function instantiated at a function type, or a branch of a dependent `match`. |
| `E_NO_TIME` | A called function has no time function, including a closure taken out of data. | Run `TimeFun` on the callee first, or declare its cost with `TimePrim`. Inside a functor, see [Limits](#limits). |
| `E_OVERAPP` | A call has more arguments than the callee's type has binders, for example a call of the result of a polymorphic function. | Don't call a function that a polymorphic function returned. In `@poly_id (nat -> nat) S n`, call `S n` directly. |
| `E_MATCH_FN` | A `match` returns a function. | Eta-expand the match: move the arguments into each branch. |
| `E_WF` | The definition recurses through a recursor without a time function, such as the `Fix_sub` of `Program Fixpoint` or the termination term of `Function`, or its result type is a function. | Use `Fix`, `loop` or `loop_fuel`. |
| `E_OPAQUE` | The constant, or a callee, is opaque or has no body. | End it with `Defined` in place of `Qed`, or declare its cost with `TimePrim`. |
| `E_SECTION` | The definition uses a section variable. | Run `TimeFun` after the section closes, or make the variable a functor parameter. |
| `E_TERM` | The term has a form that the translation doesn't support, such as `cofix`. | Rewrite the definition without it. |
| `E_ILLTYPED` | The derived time function doesn't typecheck, for example when a function argument returns a function where a polymorphic callee expects data. | Don't instantiate the data type of a polymorphic callee with a function type, as `map Nat.add l` does. |
| `E_CHECK` | The time function next to a callee is not the one derived from the callee's body. | Delete the hand-written `T_g`, and run `TimeFun g`. |
| `E_NOT_CODE` | The command targets a type or a proof. | Run it on a function. |
| `E_PLACE` | The command runs in the wrong module for a constant of another library. | Run it in a module named like the last component of the constant's path. |
| `E_TIMED` | The command repeats an earlier derivation. | Remove the second `TimeFun`. |

## Limits

- **The translator is trusted.** It is an unverified Elpi program. `TimeCheck` checks only
  that a stored time function is what the translator produces.
- **A `Parameter T_g` is used without a check.** A time function without a body next to a
  callee is used as it is. A `Parameter T_g` outside a module type is an axiom, which
  `Print Assumptions` shows and `just check` doesn't reject.
- **Functors forget registrations.** Facts that a command records inside a functor are dropped
  when the functor ends. So `TimePrim`, `TimeUnfold`, `TimeBound`, and `TimeFun` for a constant
  of another library, belong outside functors. rocq-elpi gives no way to tell that a command
  runs inside a functor, so these commands can't reject it there. The messages of `E_NO_TIME`
  and `E_OPAQUE` for a callee name this cause, and a bound registered inside a functor is not
  posed.
- **Extraction tables are invisible.** rocq-elpi gives no access to them, so no command reads
  the constants that extraction realises natively. Compare them with the `TimePrim` costs in a
  test, with `TimePrimTable`.
- **Some recursion schemes are rejected.** Well-founded recursion works through `Fix`, `Fix_F`,
  `Acc_rect` and `well_founded_induction_type`, for a result type that is not a function.
  `Program Fixpoint`, `Function` and the recursors of two arguments, such as `Fix_F_2`, are
  rejected. Equations is not packaged in the flake, so definitions by Equations are untested.
  The potential lemmas quantify over every recursive-call function, so a step whose cost
  depends on the results of its recursive calls needs a bound proved by hand.
- **Closures can't be stored in data.** A record of functions becomes a functor parameter.
- **`cofix` can't be translated**, because rocq-elpi doesn't read cofixpoints.
