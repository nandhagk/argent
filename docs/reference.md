# Argent reference

- [Cost model](#cost-model)
- [Commands](#commands)
- [Tactics](#tactics)
- [Complexity bounds](#complexity-bounds)
- [Sizes and scopes](#sizes-and-scopes)
- [Signatures with a time layer](#signatures-with-a-time-layer)
- [Amortised bounds, loops and well-founded recursion](#amortised-bounds-loops-and-well-founded-recursion)
- [Error codes](#error-codes)
- [Limits](#limits)

[The tutorial](tutorial.md) introduces the same material through examples.

## Cost model

`T_f a1 … an` is the number of steps of the call `f a1 … an` under call-by-value evaluation of the extracted program. A step is one call of a defined function or of a closure body.

| Term | Cost | Example |
| --- | --- | --- |
| A call `g a1 … an` | the costs of evaluating the arguments, plus `T_g a1 … an` | `append r l2` costs `T_append r l2`, because `r` and `l2` are variables |
| The body of `f` | 1 for the call of `f`, plus the cost of the body | `T_append [] l2 = 1` |
| `match e with … end` | the cost of `e`, plus the cost of the branch that runs | `T_pop` pays for the reversal only in the branch where the front list is empty |
| `let x := v in b` | the cost of `v`, once, plus the cost of `b` | |
| A constructor `K a1 … an` | the costs of its arguments only | `x :: append r l2` costs `T_append r l2` |
| A variable or a literal | 0 | |
| A type or a proof | 0, because extraction erases it | the proof `div2_lt x q E` in `examples/Halving.v` |
| A defined constant applied only to types and proofs, such as `@empty A` in `examples/Queue.v` | 0, because the extracted program evaluates it once, at start-up | |

Function arguments:

- A function argument `g` of `f` gets a *companion* `T_g`, its time function, right after it in `T_f`.
- So `T_map : forall {A B : Type}, (A -> B) -> (A -> N) -> list A -> N`.
- At a call site, `TimeFun` derives the companion from the argument:

| Argument | Companion | Cost of creating it |
| --- | --- | --- |
| A closure `fun x => e` | `fun x => 1 + (the cost of e)` | 0 |
| A partial application `h a` | `fun x => T_h a x` | the cost of evaluating `a`, paid once, when the closure is created |
| A constructor used as a function, `K a` | `fun x => 1` | the cost of evaluating `a` |
| A local function with a companion | that companion | 0 |

- Functions may be passed as arguments.
- Functions may not be stored in data: a closure taken out of a list or a record has no companion (`E_CLOSURE_DATA`).

Accuracy:

- `T_f` counts steps up to a constant factor. A body has no loop other than calls, so the work between two counted calls is bounded by the size of the largest body.
- The real number of steps is between `T_f` and a constant times `T_f + 1`. [The design note](design.md) argues this; it is not a theorem of the library.
- Overestimate: a function that returns a function is eta-expanded. For example, `Pos.compare := Pos.compare_cont Eq` becomes a function of two arguments, and a reused partial application pays for creating the closure at every call.
- Underestimate: a closure that a beta-redex or `TimeUnfold` substitutes isn't charged the 1 of its call, while a `let`-bound closure is. Both are within the constant factor.

Numbers:

- `nat`, `positive`, `N` and `Z` are the standard library's inductive types.
- `nat` arithmetic is unary.
- Arithmetic on `positive`, `N` and `Z` costs what its Gallina code costs. Each recursive call handles one bit: addition is linear in the number of bits, multiplication and division are quadratic.
- A constant that extraction realises natively needs a cost declared with [`TimePrim`](#timeprim).

Evaluating time functions:

- Times are binary numbers of type `N`, so `vm_compute` evaluates time functions on large inputs. `tests/TestsLarge.v` evaluates the time of `rev_append` on 1,000,000 elements.
- Evaluating `T_f` can take longer than running `f`: it recomputes the values that the callees' time functions receive. For example, `List.T_rev` computes `rev` of every suffix, so it takes cubic time where `rev` takes quadratic time.

## Commands

All commands are in `Argent.Time`: `From Argent Require Import Time.`

### `TimeFun`

`TimeFun f g …` derives `T_f`, `T_g`, … and declares each one next to its constant.

```coq
TimeFun append.
```

- Mutual definitions: one time function for every member that is a constant, as one mutual fixpoint.
- Constants of another library: run `TimeFun` in a module named like the last component of the constant's path, so that `Nat.add` gets `Nat.T_add`. `Argent.Std` does this for the standard library.
- Callees: a call of `g` is charged with the time function that an earlier `TimeFun` recorded for `g`. Otherwise it is charged with the constant `T_g` next to `g` (the *sibling rule*). The sibling rule finds the time functions of functor parameters and instances.
- Checks: when that `T_g` has a body, `TimeFun` first derives the time function of `g` again and fails with `E_CHECK` unless the two are convertible. The check reaches the callees of `g` too, so a hand-written time function is caught at any depth.
- A `T_g` without a body, such as a `Parameter` of a module type, is used as it is.
- Each check runs once per command. Its result is kept for later commands, until the end of the enclosing functor if there is one.
- Aliases: a constant whose body is another constant, as in `Module K := K0.`, is charged with the time function of that constant.
- `T_f` has the implicit arguments of `f`. Companions are explicit.
- `T_f` is universe polymorphic exactly when `f` is.
- `T_f` never unfolds under `cbn` or `simpl`. Unfold it with [`time_unfold`](#time_unfold) or [`time_step`](#time_step).

### `TimeCheck`

`TimeCheck f …` derives the time function of `f` again, and fails unless it is convertible with the stored `T_f`. A time function written or edited by hand fails this check.

```coq
TimeCheck append.
```

### `TimeAudit`

`TimeAudit r …` visits every constant that the roots `r …` call, directly or not.

- Runs `TimeCheck` on each one.
- Fails (`E_AUDIT`) on a computational constant with neither a time function nor a `TimePrim` cost.
- Run it on the functions that are extracted.

```coq
TimeAudit Trie.get Trie.set Trie.remove Queue.step.
```

### `TimePrim`

`TimePrim c := (e)` declares the cost `e` of a constant `c` with no body to read: an opaque constant, or one that extraction replaces by native code.

```coq
TimePrim opaque_double := (fun n => (N.of_nat n + 1)%N).
```

- `e` has the time type of `c`: the type of `c`, with `N` as the result and a companion after each function argument.
- `TimePrim c := n` declares a constant cost `n`, a literal of type `N`.
- A scope delimiter such as `%N` goes inside the parentheses. The command doesn't read one after them.
- The only way to write a cost by hand. Review every use.

### `TimePrimTable`

`TimePrimTable` prints every cost declared with `TimePrim`, sorted by the full name of the constant. `TimePrimTable c …` also fails unless the constants with a declared cost are exactly `c …`.

```coq
TimePrimTable opaque_double opaque_triple.
```

No command can read the extraction tables. A project that realises constants natively runs `TimePrimTable` in a test, on the constants of its `Extract Constant` directives. The test fails when a cost is declared or removed without the matching directive.

### `TimeUnfold`

`TimeUnfold c …` makes the translation unfold `c` at every call, before translating the call.

```coq
Definition bind {A B : Type} (m : M A) (f : A -> M B) : M B := f m.
TimeUnfold ret bind.
```

- A resulting beta-redex `(fun x => k) m` is charged as `let x := m in k`.
- So code in an identity monad costs the same as the code written with `let`.
- Recursive constants are rejected: inlining a fixpoint at every call would cost the same as a call of its time function, and would hide that time function from its bound.

### `TimeBound`

`TimeBound L` registers a lemma `L : forall xs, [P xs ->] (T_g args <= B)%N` for [`time_pose`](#time_pose) and `time_step`.

```coq
Definition twice (n : nat) : nat := n + n.

TimeFun twice.

Lemma twice_bound (n : nat) : (T_twice n <= N.of_nat n + 2)%N.
Proof.
  time_step.
Qed.

TimeBound twice_bound.
```

- A lemma named `T_g_le` next to `T_g` is found without registration.
- Inside a functor, the name `T_g_le` is the only way: a registration made inside a functor is dropped when the functor ends.

### `TimeFunFails`

`TimeFunFails "E_CODE" f` succeeds when `TimeFun f` fails with the error code `E_CODE`, and declares nothing. For tests.

## Tactics

`time_unfold` is in `Argent.Time`. The other tactics are in `Argent.Tactics`.

### `time_unfold`

`time_unfold @T_f` unfolds `T_f` by one step wherever its structural argument is a constructor, and folds its recursive calls back.

```coq
time_unfold @T_rev_onto.
```

- On `T_rev_onto (x :: r) acc = …`, it leaves `1 + T_rev_onto r (x :: acc) = …`.
- A time function that isn't recursive is unfolded at every application.
- The `@` passes the constant itself, without filling in its implicit arguments.

### `time_simpl`

Replaces each time function whose value is a number, such as `T_negb b` or `T_count_step n`, by that number.

### `time_cbn`

Runs `cbn` with the arithmetic of `N` kept folded, so that `lia` can read the goal.

- Computes specification functions such as `length (x :: l)`.
- Rewrites `N.of_nat (S n)` to `N.of_nat n + 1`.
- Leaves time functions folded.
- `time_cbn_all` does the same in every hypothesis.
- Why: a plain `cbn` turns `1 + t` into a `match` on `t`, and `N.of_nat (S n)` into a `positive` literal over `Pos.of_succ_nat n`. `lia` can't read either.
- Folded constants: `N.add`, `N.mul`, `N.sub`, `N.succ`, `N.pred`, `N.max`, `N.min`, `N.div`, `N.modulo`, `N.pow`, `N.of_nat`. Size functions such as `N.size_nat` and conversions such as `Z.abs_N` and `N.to_nat` still compute.

### `time_pose`

Adds a hypothesis for each time function applied in the goal:

- its bound registered with `TimeBound`;
- its sibling `T_g_le`;
- the quantified hypotheses that match it, such as a generalised induction hypothesis or a bound on a companion.

Premises of conditional bounds are discharged with `assumption`, `lia` or `eauto with time_inv`.

### `time_step`

Proves most bounds `T_f args <= e` in one line.

```coq
induction l1 as [| x r IH]; time_step.
```

- Unfolds the time function on the left by one step.
- Runs `time_simpl` and `time_cbn`, and poses bounds with `time_pose`.
- Tries `time_lin`, then `nia`.
- If both fail, destructs the scrutinees of the remaining matches and tries again.
- If it can't close the goal, it leaves it unfolded and simplified, with the bounds posed.
- `time_step f` unfolds the time function of `f` instead.

### `time_lin`

Closes a goal that is linear once each product with an abstract constant counts as one variable, such as `c_map * (bits k + 1)` with `c_map` a `Parameter` of a signature.

- Distributes the products.
- Adds `c * a <= c * b` for each hypothesis `a <= b` on `N` and each such constant `c`, and the same through `N.of_nat` for hypotheses on `nat`.
- Replaces the remaining products by fresh variables, then calls `lia`.
- Runs only when a constant multiplies a term. Fails with the goal unchanged.
- `time_step` calls it before `nia`.

### `loop_bound`

`loop_bound Inv Phi Tstop` applies [`T_loop_le`](#amortised-bounds-loops-and-well-founded-recursion) or `T_loop_fuel_le` to a goal `T_loop … s H <= e` or `T_loop_fuel … s <= e`.

- Leaves the premises of the lemma.
- Leaves the arithmetic goal `Phi s + Tstop + 1 <= e` unless `lia` solves it.

### `amortise`

`amortise Inv Phi A k` applies `amortised_uniform` to a goal `total op T os s <= e`. It leaves four goals:

- `amortised op T A Phi Inv`;
- the cap `A o s <= k`;
- `Inv s`;
- the arithmetic `k * N.of_nat (length os) + Phi s <= e`, unless `lia` solves it.

## Complexity bounds

`Argent.Complexity` defines the bounds.

- Each bound relates a time function `T` to a measure `g`, on the inputs `x` that satisfy a precondition `P`.
- The input is the tuple of all arguments, so the constant doesn't depend on any of them.

| Bound | Constant | Meaning, for the inputs that satisfy `P` |
| --- | --- | --- |
| 𝑂 | `bigO P g T` | `T x <= c * (g x + 1)` for one constant `c` |
| Ω | `bigOmega P g T` | `g x <= c * (T x + 1)` for one constant `c` |
| Θ | `bigTheta P g T` | both of the above |
| Ω in the worst case | `bigOmega_worst P g T` | for every `n`, some input with `n <= g x` has `g x <= c * T x`, for one constant `c` |
| Θ in the worst case | `tight P g T` | 𝑂, and Ω in the worst case |
| amortised 𝑂 | `bigO_amortised P g T before after` | `T x + after x <= c * (g x + 1) + before x` for one constant `c` |

- Worst case: a trie lookup that misses can stop after one step, so it has no lower bound in the key length on every input. On a trie that holds the key it reads every bit, which is a lower bound in the worst case.
- Amortised: `before x` is the potential that an operation finds, and `after x` the potential that it leaves.

### Notation

After `From Argent Require Import Complexity.` and `Import ComplexityNotations.`:

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

This is the term `bigO (fun _ => True) (fun '(p, m) => N.of_nat (Pos.size_nat p)) (fun '(p, m) => T_get p m)`.

- `x` is a name or a tuple pattern without a quote, such as `(p, m)`. It binds the variables of the time, the measure, the precondition and the potentials.
- A pattern can't give types. A statement names an implicit argument, as `(A := A)` above, when nothing else fixes it.
- Without `| P`, the precondition is `True`.
- `𝑂` is U+1D442 (mathematical italic capital O), a different character from the constructor `O` of `nat`. With the ASCII letter, `O(` would be one token, and `S O(* … *)` would no longer parse.
- Levels: a bound is at level 70 with no associativity, like `=` and `<=`. The time is read at level 69, so a sum of times needs no parentheses. The measure is read at level 200 inside its parentheses, the potentials at level 69.
- The precondition is read at level 200, so it extends to the end of the statement, like the body of `forall`. A bound with a precondition needs parentheses when more text follows, such as `->` and a conclusion. A bound without one is a term of level 70, joined by `/\` and `->` like an equation.
- Scopes: the time, the measure and the potentials are read in `N_scope`; the precondition in the scope of the statement.
- Rocq prints every bound in the notation, also one written with `fst` and `snd`, and breaks a long line before `for`.

### Lemmas

Prove a bound with explicit constants first, then state the complexity as a corollary.

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

- Time functions, time constants, potentials and bounds have type `N`.
- A size of type `nat`, such as `length l`, `Pos.size_nat p`, `N.size_nat n` or the bit length of a `Z`, enters a bound as `N.of_nat` of the size.
- A size that is already an `N`, such as the argument `x : N` of a function that halves it, enters a bound as it is.
- A file of bounds can open `N_scope` and mark statements about sizes alone with `%nat`, as `Argent.Std` does.

## Signatures with a time layer

A module type has two layers:

- the functional layer: the operations and their laws;
- the time layer: a time function per operation, a named constant, and a contract that bounds the time function by that constant.

```coq
Module Type MAP.
  Declare Module K : KEY.
  Parameter t : Type -> Type.
  Parameter get : forall {A : Type}, K.t -> t A -> option A.
  Parameter set : forall {A : Type}, K.t -> A -> t A -> t A.
  Parameter get_set_same : forall A k (v : A) m, get k (set k v m) = Some v.
  (* The time layer. *)
  Parameter T_get : forall {A : Type}, K.t -> t A -> N.
  Parameter T_set : forall {A : Type}, K.t -> A -> t A -> N.
  Parameter c_map : N.
  Parameter T_get_le :
    forall A k (m : t A), (T_get k m <= c_map * (N.of_nat (Pos.size_nat (K.encode k)) + 1))%N.
  Parameter T_set_le :
    forall A k (v : A) m,
      (T_set k v m <= c_map * (N.of_nat (Pos.size_nat (K.encode k)) + 1))%N.
End MAP.
```

- An implementation defines the operations, runs `TimeFun` on them (which derives `T_get` and `T_set`), and proves the contracts for its own `c_map`.
- A client is a functor over the signature. Its `TimeFun` charges a call of `M.get` with `M.T_get` through the sibling rule.
- The client's bounds can use only the contracts, so they hold for every implementation.
- The contracts are `Parameter`s of the module type, so they add no axiom: every instance must prove them.
- Full example: `examples/KeyedMap.v`.

## Amortised bounds, loops and well-founded recursion

All of these bound a cost with a potential `Phi`, a number attached to each state.

### Amortised bounds

In `Argent.Amortised`. Write the operations as one function `step : op -> S -> S` over an inductive type `op`, and run `TimeFun step`. Then:

1. Choose a potential `Phi : S -> N`, an invariant `Inv`, and an amortised cost `A o s : N`.
2. Prove `amortised step T_step A Phi Inv`: every operation keeps `Inv`, and `T_step o s + Phi (step o s) <= A o s + Phi s`.
3. Apply `amortised_run` for the exact statement on a sequence, or `amortised_uniform` (through the tactic `amortise`) for `total step T_step os s <= k * N.of_nat (length os) + Phi s`.

- The bound holds along one sequence of versions.
- It says nothing about a history that uses one version twice: an expensive operation repeated on the same version isn't paid for.

### Loops

In `Argent.Loop`.

- `loop lt step s H` runs `step` until it returns a result, recursing on the accessibility proof `H`.
- `loop_fuel step fuel s` runs it at most `fuel` times.
- `T_loop_le` and `T_loop_fuel_le`: if each step that continues keeps `Inv` and satisfies `T_step s + Phi s1 < Phi s`, and each step that stops costs at most `Tstop`, then the loop from `s` costs at most `Phi s + Tstop + 1`.
- The potential must drop by more than the step costs, because each iteration also costs one call.
- The bounds hold for every proof and every amount of fuel.

### Well-founded recursion

In `Argent.Std`, module `Wf`.

- `Std` derives the time functions of `Fix_F`, `Fix`, `Acc_rect` and `well_founded_induction_type`, so `TimeFun` handles definitions written with them.
- The companion `T_F` of the functional `F` takes the companion `T_rec` of its recursive-call argument.
- Each recursive call costs `1 + T_Fix_F … y _`. The 1 is the call of the closure that `Fix_F` passes to `F`.
- `Wf.T_Fix_le`: `T_Fix Rwf P F T_F x <= Phi x + 1` when every step satisfies `T_F x rec T_rec + 1 <= Phi x`, for every `rec` and every `T_rec` with `T_rec y h <= Phi y + 1`.
- `Wf.T_Fix_F_le`, `Wf.T_Acc_rect_le` and `Wf.T_well_founded_induction_type_le`: the same for the other recursors.
- Example: `examples/Halving.v`.

Computing with `Fix`:

- A `Fix` over a well-foundedness proof that never reduces to a constructor gets stuck under `vm_compute`. `N.lt_wf_0` is such a proof: it is built from a lemma that ends in `Qed`.
- `Acc_intro_generator n` adds `2 ^ n` constructors in front of the proof, lazily. The function then computes when its recursion is less than `2 ^ n` calls deep.
- Extraction erases the proof. The extracted `log2` of `examples/Halving.v` is `let rec log2 x = log2_step x (fun y _ -> log2 y)`.

## Error codes

`TimeFun` rejects a definition whose cost it can't account for. `TimeAudit` rejects a root that reaches a constant without a cost.

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
| `E_TERM` | The term has a form that the translation doesn't support, such as a `let` in a function argument: `map (let g := S in g) l`. | Move the `let` out of the call: `let g := S in map g l` is accepted. A definition with `cofix` fails before translation, with no code. |
| `E_ILLTYPED` | The derived time function doesn't typecheck, for example when a function argument returns a function where a polymorphic callee expects data. | Don't instantiate the data type of a polymorphic callee with a function type, as `map Nat.add l` does. |
| `E_CHECK` | The time function next to a callee is not the one derived from the callee's body. | Delete the hand-written `T_g`, and run `TimeFun g`. |
| `E_NOT_CODE` | The command targets a type or a proof. | Run it on a function. |
| `E_PLACE` | The command runs in the wrong module for a constant of another library. | Run it in a module named like the last component of the constant's path. |
| `E_TIMED` | The command repeats an earlier derivation. | Remove the second `TimeFun`. |
| `E_AUDIT` | `TimeAudit` reached a computational constant that has neither a time function nor a `TimePrim` cost. | Run `TimeFun` on that constant, or declare its cost with `TimePrim`. |

## Limits

- The translator is trusted: an unverified Elpi program. `TimeCheck` checks only that a stored time function is what the translator produces.
- A time function without a body next to a callee, such as a `Parameter T_g`, is used without a check. A `Parameter T_g` outside a module type is an axiom: `Print Assumptions` shows it, and `just check` doesn't reject it.
- Facts recorded inside a functor are dropped when the functor ends.
  - `TimePrim`, `TimeUnfold`, `TimeBound`, and `TimeFun` for a constant of another library, belong outside functors.
  - rocq-elpi gives no way to detect a functor, so these commands can't reject a run inside one.
  - The messages of `E_NO_TIME` and `E_OPAQUE` for a callee name this cause, and a bound registered inside a functor is not posed.
- No command reads the extraction tables (rocq-elpi gives no access to them). Compare them with the `TimePrim` costs in a test, with `TimePrimTable`.
- Recursion schemes:
  - Well-founded recursion works through `Fix`, `Fix_F`, `Acc_rect` and `well_founded_induction_type`, for a result type that is not a function.
  - `Program Fixpoint`, `Function` and the two-argument recursors, such as `Fix_F_2`, are rejected.
  - Equations isn't packaged in the flake, so definitions by Equations are untested.
  - The potential lemmas quantify over every recursive-call function. A step whose cost depends on the results of its recursive calls needs a bound proved by hand.
- Closures can't be stored in data. A record of functions becomes a functor parameter.
- `cofix` can't be translated: rocq-elpi doesn't read cofixpoints.
