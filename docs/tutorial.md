# Argent tutorial

By the end of this tutorial you can derive the time function of a Rocq function, prove bounds
on it, and state its complexity, including amortised bounds and bounds for loops and
well-founded recursion. You need to know basic Rocq: inductive types, `Fixpoint`, proofs by
induction, and `lia`.

Each step adds one idea, and its code comes from one of the files in [`examples/`](../examples),
so you can read the full file next to the step. Steps 1 to 5 use
[`examples/Lists.v`](../examples/Lists.v).

## 1. Your first time function

Here is `append`, written as usual:

```coq
Fixpoint append {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: r => x :: append r l2
  end.
```

One command derives its time function:

```coq
TimeFun append.
```

`TimeFun append` reads the body of `append` and defines a new constant, `T_append`, next to it.
`T_append l1 l2` is the number of steps that `append l1 l2` takes. `Print T_append` shows it:

```text
T_append =
fix T_append (A : Type) (l1 l2 : list A) {struct l1} : N :=
  (1 + match l1 with
       | [] => 0
       | _ :: r => T_append A r l2
       end)%N
```

`T_append` has the same shape as `append`, with costs in place of values:

- The `1 +` is the call of `append` itself. Every call of a function costs one step.
- The `match` stays, because the cost depends on which branch runs.
- Returning `l2` costs nothing more: variables and constructors are free.
- The recursive call `append r l2` costs `T_append r l2`. The `x ::` in front of it is a
  constructor, so it adds nothing.

That is the whole cost model, in short: one step per call, and every call is charged with the
time function of the function it calls. Types and proofs cost nothing, because extraction
erases them. [The reference](reference.md#cost-model) lists every rule.

Times are binary numbers of type `N`, so a time function computes quickly even on large inputs.
The example file checks one value:

```coq
Example T_append_three : T_append [1; 2; 3] [4; 5] = 4 := eq_refl.
```

There are four calls: on `[1; 2; 3]`, `[2; 3]`, `[3]` and `[]`.

To reason about `T_append`, it helps to write its two cases as equations. Both hold by
computation, so `reflexivity` proves them:

```coq
Lemma T_append_nil {A : Type} (l2 : list A) : T_append [] l2 = 1.
Proof.
  reflexivity.
Qed.

Lemma T_append_cons {A : Type} (x : A) (r l2 : list A) :
  T_append (x :: r) l2 = 1 + T_append r l2.
Proof.
  reflexivity.
Qed.
```

## 2. Proving a bound

A bound on `T_append` is proved like any fact about a recursive function, by induction:

```coq
Theorem T_append_exact {A : Type} (l1 l2 : list A) :
  T_append l1 l2 = N.of_nat (length l1) + 1.
Proof.
  induction l1 as [| x r IH].
  - rewrite T_append_nil. reflexivity.
  - (* 1 + T_append r l2 = 1 + (length r + 1) *)
    rewrite T_append_cons, IH. cbn [length]. lia.
Qed.
```

`length` returns a `nat`, but times are `N`, so the size enters the bound as
`N.of_nat (length l1)`. Every statement about time follows this convention, and `lia` reasons
through `N.of_nat`.

Most bounds follow the same three moves: unfold the time function once, use the induction
hypothesis or a bound on a callee, then do the arithmetic. The tactic `time_step` makes those
moves for a goal of the form `T_f args <= bound`. It unfolds `T_f` once, adds the bounds that it
knows for the other time functions in the goal, and finishes with `lia` or `nia`, which use the
hypotheses in context, such as the induction hypothesis:

```coq
Theorem T_append_le {A : Type} (l1 l2 : list A) :
  T_append l1 l2 <= N.of_nat (length l1) + 1.
Proof.
  induction l1 as [| x r IH]; time_step.
Qed.
```

`time_step` proves only `<=` goals. An exact cost, such as `T_append_exact`, needs the proof by
hand. That's fine, because published bounds are usually upper bounds anyway.

## 3. Stating the complexity

A bound with explicit constants is the most useful form inside proofs. For readers, the
library also has the usual asymptotic notation:

```coq
Theorem append_complexity {A : Type} :
  T_append (A := A) l1 l2 ∈ 𝑂(N.of_nat (length l1)) for (l1, l2).
Proof.
  apply bigO_intro with (c := 1). intros [l1 l2] _. rewrite T_append_exact. lia.
Qed.
```

Read it as "`T_append l1 l2` is in 𝑂 of the length of `l1`, over all pairs `(l1, l2)`". By
definition, it means that one constant `c` works for every input:
`T_append l1 l2 <= c * (N.of_nat (length l1) + 1)`. The `+ 1` lets an input of size 0 cost a
constant. The proof gives the constant to `bigO_intro` and then proves the bound with that
constant.

A few details of the notation:

- `for (l1, l2)` names the arguments that the bound ranges over. A pattern can't carry types,
  so the statement fixes the implicit argument `A` of `T_append` with `(A := A)`.
- A precondition goes after a bar, as in `for x | P x`. Without one, the bound covers every
  input.
- The letter `𝑂` is U+1D442 (mathematical italic capital O), a different character from the
  constructor `O` of `nat`. Copy it from an example if your editor can't type it.
- The notation lives in `ComplexityNotations`, so a file starts with
  `From Argent Require Import Complexity.` and `Import ComplexityNotations.`

The same notation writes lower bounds (Ω), tight bounds (Θ), bounds in the worst case and
amortised bounds. Steps 6 and 7 use two of them, and
[the reference](reference.md#complexity-bounds) lists all of them.

## 4. Comparing two algorithms

Here are two ways to reverse a list. `slow_rev` appends each element after the reversed rest:

```coq
Fixpoint slow_rev {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: r => append (slow_rev r) [x]
  end.
```

Its time function charges the call of `append` with `T_append`, applied to the arguments that
`append` receives:

```coq
Lemma T_slow_rev_cons {A : Type} (x : A) (r : list A) :
  T_slow_rev (x :: r) = 1 + (T_slow_rev r + T_append (slow_rev r) [x]).
```

The term `T_append (slow_rev r) [x]` grows with the length of `r`, so the total is quadratic.
The proof needs one fact about values as well as costs: reversing doesn't change the length.

```coq
Theorem T_slow_rev_le {A : Type} (l : list A) :
  T_slow_rev l <= (N.of_nat (length l) + 1) * (N.of_nat (length l) + 1).
Proof.
  induction l as [| x r IH].
  - (* Both sides compute to 1. *)
    reflexivity.
  - (* The append costs length r + 1, by T_append_exact. *)
    rewrite T_slow_rev_cons, T_append_exact, length_slow_rev. cbn [length]. lia.
Qed.
```

`rev_onto` moves the elements onto an accumulator instead, and calls nothing else:

```coq
Fixpoint rev_onto {A : Type} (l acc : list A) : list A :=
  match l with
  | [] => acc
  | x :: r => rev_onto r (x :: acc)
  end.
```

So it takes linear time. This proof uses `time_unfold @T_rev_onto`, which unfolds `T_rev_onto`
once, as rewriting with an equation like `T_append_cons` would, without stating the equation
first:

```coq
Theorem T_rev_onto_exact {A : Type} (l acc : list A) :
  T_rev_onto l acc = N.of_nat (length l) + 1.
Proof.
  revert acc. induction l as [| x r IH]; intros acc.
  - reflexivity.
  - time_unfold @T_rev_onto. rewrite IH. cbn [length]. lia.
Qed.
```

Time functions never unfold under `cbn` or `simpl`. That keeps goals readable, and it is why
you unfold them on purpose, with `time_unfold`, `time_step` or an equation.

## 5. Functions as arguments

What `map f l` costs depends on what `f` costs:

```coq
Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: r => f x :: map f r
  end.
```

So `T_map` takes one more argument, right after `f`: a time function for `f`, called the
*companion* of `f`.

```text
T_map : forall {A B : Type}, (A -> B) -> (A -> N) -> list A -> N
T_map f T_f (x :: r) = 1 + (T_f x + T_map f T_f r)
```

A bound on `T_map` assumes a bound on the companion:

```coq
Theorem T_map_le {A B : Type} (f : A -> B) (T_f : A -> N) (k : N) (l : list A) :
  (forall x, T_f x <= k) -> T_map f T_f l <= (k + 1) * N.of_nat (length l) + 1.
```

You never write a companion yourself. Where `map` is called, `TimeFun` derives it from the
argument. A closure `fun m => e` gets `fun m => 1 + (the cost of e)`, and a named function `g`
gets its own time function `T_g`:

```coq
Definition add_to_all (n : nat) (l : list nat) : list nat := map (fun m => (n + m)%nat) l.
```

```text
T_add_to_all n l = 1 + T_map (fun m => n + m) (fun m => 1 + Nat.T_add n m) l
```

Addition on `nat` recurses on its first argument, so `Nat.T_add n m` is at most `n + 1`
(`Nat.T_add_le` in `Argent.Std`). To bound `T_add_to_all`, bound one call of the closure and
apply `T_map_le`:

```coq
Theorem T_add_to_all_le (n : nat) (l : list nat) :
  T_add_to_all n l <= (N.of_nat n + 3) * N.of_nat (length l) + 2.
Proof.
  rewrite T_add_to_all_eq.
  assert (Hcall : forall m, 1 + Nat.T_add n m <= N.of_nat n + 2).
  { intros m. pose proof (Nat.T_add_le n m). lia. }
  pose proof (T_map_le (fun m => (n + m)%nat) (fun m => 1 + Nat.T_add n m) (N.of_nat n + 2) l
    Hcall) as Hmap.
  lia.
Qed.
```

A function may be passed as an argument, but it may not be stored in a data structure: a
closure taken out of a list or a record would have no companion. `TimeFun` rejects such code
with the error `E_CLOSURE_DATA`. Step 8 shows what to do instead.

## 6. Numbers, and lower bounds

[`examples/Trie.v`](../examples/Trie.v) stores values in a binary trie under keys of type
`positive`. `get` reads the key one bit at a time, so its cost depends on the bit length of the
key, `Pos.size_nat p`:

```text
T_get =
fix T_get (A : Type) (p : positive) (m : t A) {struct p} : N :=
  (1 +
   match m with
   | Leaf => 0
   | Node l _ r =>
       match p with
       | q~1%positive => T_get A q r
       | q~0%positive => T_get A q l
       | 1%positive => 0
       end
   end)%N
```

The upper bound is routine, so `time_step` proves it. The induction runs on the key, for every
trie:

```coq
Theorem T_get_le {A : Type} (p : positive) (m : t A) :
  T_get p m <= N.of_nat (Pos.size_nat p).
Proof.
  revert m. induction p as [p IH | p IH |]; intros [| l o r]; time_step.
Qed.
```

A lookup that misses can stop at the first leaf, so no lower bound holds on every input. In
the worst case there is one: on a trie that holds the key, `get` reads every bit (`T_get_ge` in
the file). The worst-case bound Θ_worst says both things at once, the upper bound on every
input and the lower bound on some input of every size:

```coq
Theorem get_worst_complexity {A : Type} (a : A) :
  T_get (A := A) p m ∈ Θ_worst(N.of_nat (Pos.size_nat p)) for (p, m).
```

Its proof, by `tight_intro`, gives those slow inputs explicitly: the key `1~1~...~1` with `n`
ones, in a trie that holds it.

A side note on numbers: `positive`, `N` and `Z` are inductive types in the standard library, so
in this model their arithmetic costs one step per bit, and `nat` arithmetic is unary. If you
extract them to native integers, see `TimePrim` in [the reference](reference.md#timeprim).

## 7. Amortised bounds

[`examples/Queue.v`](../examples/Queue.v) is a queue made of two lists. `push` adds to the back
list, and `pop` takes from the front list. When the front is empty, `pop` reverses the back
list into the front first:

```text
T_pop =
fun (A : Type) (q : queue A) =>
(1 +
 (let (f, b) := q in
  match f with
  | [] => List.T_rev_append b []
  | _ :: _ => 0
  end))%N
```

So one `pop` can take time linear in the size of the queue. Each element is reversed at most
once, though, so a whole sequence of operations costs a constant per operation. The
*potential method* proves this. Pick a potential, a number attached to each state, here the
length of the back list:

```coq
Definition back_length {A : Type} (q : queue A) : N := N.of_nat (length (snd q)).
```

Then show that every operation costs at most a constant, 4, once you add the potential that it
creates and subtract the potential that it uses up. A `push` costs 2 and raises the potential by
1. A `pop` that reverses `b` costs `length b + 3` and lowers the potential by `length b`. The
operations go behind one function, `step`, and the property is called `amortised`:

```coq
Theorem step_amortised {A : Type} :
  amortised (@step A) T_step (fun _ _ => 4%N) back_length (fun _ => True).
```

The last argument is an invariant that every operation keeps, here `True`. Summing over a
sequence gives the bound. The tactic `amortise` applies the summing lemma and leaves four small
goals, each commented in the file:

```coq
Theorem queue_total {A : Type} (os : list (op A)) :
  (total (@step A) T_step os empty <= 4 * N.of_nat (length os))%N.
```

The bound holds along one sequence of operations, where each operation works on the queue that
the previous one returned. It says nothing about using one old queue twice, because repeating
an expensive `pop` on the same queue is never paid for.

## 8. Generic code

[`examples/KeyedMap.v`](../examples/KeyedMap.v) is about code that is generic over a module.
Such code can't look inside its parameter, so its bounds must come from the parameter's
signature. A signature therefore has a *time layer* next to its operations and laws: a time
function for each operation, a named constant, and a contract that bounds the time function by
that constant.

```coq
  Parameter T_get : forall {A : Type}, K.t -> t A -> N.
  Parameter T_set : forall {A : Type}, K.t -> A -> t A -> N.
  Parameter c_map : N.
  Parameter T_get_le :
    forall A k (m : t A), (T_get k m <= c_map * (N.of_nat (Pos.size_nat (K.encode k)) + 1))%N.
```

An implementation, such as `TrieMap`, runs `TimeFun get set`, which defines `T_get` and `T_set`
with the names that the signature expects, and then proves the contracts for its own value of
`c_map`. A client functor, such as `SumValues`, runs `TimeFun` on its own functions. A call of
`M.get` is charged with `M.T_get`, so the client's bound can use only the contract:

```coq
  Theorem T_sum_values_le (ks : list M.K.t) (m : M.t nat) :
    (T_sum_values ks m <=
     (M.c_map + 2) * N.of_nat (key_work ks) + N.of_nat (sum_values ks m) + 1)%N.
```

This bound holds for every implementation of the signature. The contracts are `Parameter`s of a
module type, so they add no axiom: every instance must prove them. This is also how to handle
a record of functions, which can't be stored in data (step 5): make it a functor parameter.

## 9. Loops

A loop that doesn't recurse on a smaller piece of its input needs another reason to stop.
[`examples/Loops.v`](../examples/Loops.v) uses `Argent.Loop`, which offers two. `loop` recurses
on a proof that the state decreases (an accessibility proof), and `loop_fuel` takes a `nat`
bound on the number of iterations (fuel). Each iteration is a call of a step function that
either continues with a smaller state or stops with a result:

```coq
Definition count_step (n : nat) : {m : nat | m < n} + nat :=
  match n as k return {m : nat | m < k} + nat with
  | 0 => inr 0
  | S m => inl (exist _ m (PeanoNat.Nat.lt_succ_diag_r m))
  end.
```

```coq
Definition countdown (n : nat) : nat := loop lt count_step n (Acc_intro_generator 32 lt_wf n).
```

`Acc_intro_generator 32` makes the accessibility proof compute, so that `countdown` runs under
`vm_compute`. Extraction erases the proof, so the extracted `countdown` is a plain recursive
function with no fuel.

The time of a loop comes from a potential `Phi` on states, through `T_loop_le` (or
`T_loop_fuel_le` for fuel). Suppose that every step that continues makes `Phi` drop by more
than the step costs, and that the step that stops costs at most `Tstop`. Then the whole loop
costs at most `Phi s + Tstop + 1` from the state `s`. The bound depends neither on the proof
nor on the fuel. For the countdown, `Phi k = 2 * k` pays for each step and for its call:

```coq
Theorem T_countdown_le (n : nat) : (T_countdown n <= 2 * N.of_nat n + 3)%N.
Proof.
  rewrite T_countdown_unfold.
  (* [T_loop_le] bounds the loop by [Phi n + Tstop + 1], with [Phi k = 2 * k] and [Tstop = 1]. *)
  enough (Hloop : (T_loop lt count_step T_count_step n (Acc_intro_generator 32 lt_wf n)
                   <= 2 * N.of_nat n + 1 + 1)%N) by lia.
  apply (T_loop_le lt count_step T_count_step (fun _ => True) (fun k => 2 * N.of_nat k)%N 1%N).
  - (* A step from [S k] continues with [k]: it costs 1, and the potential drops by 2. *)
    intros [| k] s1 Hlt _ Hstep; cbn in Hstep; [discriminate |].
    injection Hstep as <-. split; [exact I |]. time_simpl. lia.
  - (* The step at 0 stops, and costs 1. *)
    intros s r _ _. time_simpl. lia.
  - (* The invariant is [True]. *)
    exact I.
Qed.
```

`T_countdown_unfold` states what `T_countdown` is: one step for the call, plus the time function
of `loop`. `time_simpl` replaces a time function whose value is a number, here `T_count_step`,
by that number.

## 10. Well-founded recursion

[`examples/Halving.v`](../examples/Halving.v) defines a binary logarithm that recurses on half of
its argument. Half of a number isn't a structural subterm, so the definition uses `Fix` over
`N.lt`. Each recursive call needs a proof that its argument is smaller:

```coq
Definition log2_step (x : N) (rec : forall y : N, (y < x)%N -> nat) : nat :=
  match x as x' return x = x' -> nat with
  | N0 => fun _ => 0
  | N.pos q => fun E =>
    match q with
    | xH => 0
    | _ => S (rec (N.div2 x) (div2_lt x q E))
    end
  end eq_refl.
```

```coq
Definition log2 (x : N) : nat :=
  Fix (Acc_intro_generator 64 N.lt_wf_0) (fun _ => nat) log2_step x.
```

The match on `x` has the clause `return x = x' -> nat`, and `eq_refl` comes after it. So each
branch receives an equation for its own case, here `E : x = N.pos q`, which is what the proof
of decrease needs. This pattern is called a convoy match.

`TimeFun log2_step` gives the recursive-call argument `rec` its own companion `T_rec`. A call
`rec y h` costs `T_rec y h`, and the proof `h` costs nothing. `Wf.T_Fix_le` in `Argent.Std`
bounds the whole recursion with a potential, in the same way as the loop lemmas. If each step
costs at most `Phi x`, assuming that each recursive call on `y` costs at most `Phi y + 1`, then
`T_Fix … x <= Phi x + 1`. For `log2`, `Phi x = 4 * size x + 2`:

```coq
Theorem T_log2_le (x : N) : T_log2 x <= 4 * N.of_nat (N.size_nat x) + 4.
```

`Program Fixpoint` and `Function` build their recursion differently, and `TimeFun` rejects them
with `E_WF`. Write such functions with `Fix`, `loop` or `loop_fuel`.

## 11. Before you trust a bound

A bound on `T_f` is a theorem about `T_f`. Four checks tie it to the program that you actually
run.

- **What is counted.** `T_f` counts calls under call-by-value evaluation of the extracted
  program. The real number of machine steps is at least `T_f` and at most a constant times
  `T_f + 1`, where the constant is the size of the largest function body involved. So a bound
  on `T_f` is a bound on the real running time, up to a constant factor. The design note argues
  this. It is not a theorem of the library.
- **Run `TimeAudit` on the functions that you extract.** `TimeAudit f g …` visits every constant
  that they call, directly or not. It checks each time function again against its constant's
  body, and fails on any computational constant that has no time function. A time function
  can't be edited by hand without `TimeAudit` or `TimeCheck` noticing.
- **Review `TimePrim`.** `TimePrim c := (e)` declares the cost of a constant that has no body
  to read, such as one that extraction replaces by native code. It is the only way to write a
  cost by hand, so its uses are what to review.
- **Run `Print Assumptions`.** A bound should depend on no axiom. The contracts of a signature
  are not axioms, because they are `Parameter`s of a module type. A `Parameter` outside a module
  type is an axiom, though, and `Print Assumptions` shows it.

`TimeFun` itself is an unverified program, written in Elpi, and you trust it. `TimeCheck`
confirms only that a stored time function is what `TimeFun` produces.

## Where to go next

- [`reference.md`](reference.md) has the cost model in full, every command, tactic and bound,
  and what each error code means.
- [`design.md`](design.md) explains how `TimeFun` translates a definition, and why the costs
  match the extracted program.
