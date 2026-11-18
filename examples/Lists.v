(** * Time functions of list functions

    Read this example first.  It derives the time functions of [append], of two ways to
    reverse a list and of [map], and proves a bound on each.  Each section adds one idea:
    reading a time function, proving a bound, stating the complexity, comparing two algorithms,
    and passing a function as an argument.

    For example, [TimeFun append] defines [T_append], and [T_append [1; 2; 3] [4; 5] = 4]:
    one step for each element of the first list, and one for the final call on [[]].

    Builds on: Time Tactics Complexity Std *)

From Stdlib Require Import NArith Lia.
From Stdlib Require List.
From Argent Require Import Time Tactics Complexity Std.
Import List.ListNotations ComplexityNotations.

(** Times are binary numbers of type [N], so [+] and [*] below are on [N].  A sum of [nat]s
    is marked [%nat]. *)
Local Open Scope list_scope.
Local Open Scope N_scope.

(** * Reading a time function *)

(** [append l1 l2] puts the elements of [l1] in front of [l2]. *)
Fixpoint append {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: r => x :: append r l2
  end.

(** [TimeFun append] reads the body of [append] and defines [T_append l1 l2], the number of
    steps that [append l1 l2] takes.  [Print T_append] shows:

      T_append =
      fix T_append (A : Type) (l1 l2 : list A) {struct l1} : N :=
        (1 + match l1 with
             | [] => 0
             | _ :: r => T_append A r l2
             end)%N

    Every call costs 1, and a call on [x :: r] also pays for the recursive call on [r]. *)
TimeFun append.

Example T_append_three : T_append [1; 2; 3] [4; 5] = 4 := eq_refl.

(** The same definition, as one equation per case.  [reflexivity] proves both, because they
    hold by computation. *)
Lemma T_append_nil {A : Type} (l2 : list A) : T_append [] l2 = 1.
Proof.
  reflexivity.
Qed.

Lemma T_append_cons {A : Type} (x : A) (r l2 : list A) :
  T_append (x :: r) l2 = 1 + T_append r l2.
Proof.
  reflexivity.
Qed.

(** * Proving a bound *)

(** [append l1 l2] takes one step per element of [l1], plus one. *)
Theorem T_append_exact {A : Type} (l1 l2 : list A) :
  T_append l1 l2 = N.of_nat (length l1) + 1.
Proof.
  induction l1 as [| x r IH].
  - rewrite T_append_nil. reflexivity.
  - (* T_append (x :: r) l2 is 1 + T_append r l2, and the IH gives T_append r l2. *)
    rewrite T_append_cons, IH. cbn [length]. lia.
Qed.

(** [time_step] does those steps for a goal [T_f args <= bound]: it unfolds [T_f] once, adds
    the bounds that it knows for the other time functions in the goal, and solves the
    arithmetic with the hypotheses in context, such as the induction hypothesis.  It knows a
    bound on [T_g] when a lemma named [T_g_le] sits next to [T_g], or when one was registered
    with [TimeBound].  Most bounds take one line. *)

(** [append l1 l2] takes at most one step per element of [l1], plus one. *)
Theorem T_append_le {A : Type} (l1 l2 : list A) :
  T_append l1 l2 <= N.of_nat (length l1) + 1.
Proof.
  induction l1 as [| x r IH]; time_step.
Qed.

(** * Stating the complexity *)

(** [append] runs in time 𝑂(length of the first list).  [for (l1, l2)] names the arguments of
    the time function.  A pattern can't carry types, so the statement gives the implicit
    argument [A] of [T_append] explicitly. *)
Theorem append_complexity {A : Type} :
  T_append (A := A) l1 l2 ∈ 𝑂(N.of_nat (length l1)) for (l1, l2).
Proof.
  apply bigO_intro with (c := 1). intros [l1 l2] _. rewrite T_append_exact. lia.
Qed.

(** * Comparing two algorithms *)

(** [slow_rev] reverses a list by appending each element after the reversed rest. *)
Fixpoint slow_rev {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: r => append (slow_rev r) [x]
  end.

(** The call of [append] appears in [T_slow_rev] as [T_append], applied to the reversed rest:

      T_slow_rev (x :: r) = 1 + (T_slow_rev r + T_append (slow_rev r) [x])

    That term grows with the length of [r], so the total is quadratic. *)
TimeFun slow_rev.

Lemma T_slow_rev_cons {A : Type} (x : A) (r : list A) :
  T_slow_rev (x :: r) = 1 + (T_slow_rev r + T_append (slow_rev r) [x]).
Proof.
  reflexivity.
Qed.

Lemma length_append {A : Type} (l1 l2 : list A) :
  length (append l1 l2) = (length l1 + length l2)%nat.
Proof.
  induction l1 as [| x r IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Lemma length_slow_rev {A : Type} (l : list A) : length (slow_rev l) = length l.
Proof.
  induction l as [| x r IH].
  - reflexivity.
  - cbn [slow_rev]. rewrite length_append, IH. cbn. lia.
Qed.

(** [slow_rev] takes time quadratic in the length of the list. *)
Theorem T_slow_rev_le {A : Type} (l : list A) :
  T_slow_rev l <= (N.of_nat (length l) + 1) * (N.of_nat (length l) + 1).
Proof.
  induction l as [| x r IH].
  - (* Both sides compute to 1, and [reflexivity] also proves [1 <= 1]. *)
    reflexivity.
  - (* The append costs length r + 1, by T_append_exact. *)
    rewrite T_slow_rev_cons, T_append_exact, length_slow_rev. cbn [length]. lia.
Qed.

(** [rev_onto l acc] reverses [l] onto the front of [acc]. *)
Fixpoint rev_onto {A : Type} (l acc : list A) : list A :=
  match l with
  | [] => acc
  | x :: r => rev_onto r (x :: acc)
  end.

(** [T_rev_onto (x :: r) acc = 1 + T_rev_onto r (x :: acc)]: no other call, so the total is
    linear. *)
TimeFun rev_onto.

(** [rev_onto] takes one step per element of [l], plus one.  [time_unfold @T_rev_onto]
    unfolds [T_rev_onto] once, as rewriting with an equation such as [T_append_cons] would,
    without stating the equation first.  The [@] passes the constant [T_rev_onto] itself,
    without filling in its implicit argument. *)
Theorem T_rev_onto_exact {A : Type} (l acc : list A) :
  T_rev_onto l acc = N.of_nat (length l) + 1.
Proof.
  revert acc. induction l as [| x r IH]; intros acc.
  - reflexivity.
  - time_unfold @T_rev_onto. rewrite IH. cbn [length]. lia.
Qed.

(** * Passing a function as an argument *)

(** [map f l] applies [f] to every element of [l]. *)
Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: r => f x :: map f r
  end.

(** What [map] costs depends on what [f] costs.  So [T_map] takes one more argument, right
    after [f]: a time function [T_f] for [f], called the companion of [f].

      T_map : forall {A B : Type}, (A -> B) -> (A -> N) -> list A -> N
      T_map f T_f (x :: r) = 1 + (T_f x + T_map f T_f r) *)
TimeFun map.

Lemma T_map_nil {A B : Type} (f : A -> B) (T_f : A -> N) : T_map f T_f [] = 1.
Proof.
  reflexivity.
Qed.

Lemma T_map_cons {A B : Type} (f : A -> B) (T_f : A -> N) (x : A) (r : list A) :
  T_map f T_f (x :: r) = 1 + (T_f x + T_map f T_f r).
Proof.
  reflexivity.
Qed.

(** When every call of [f] takes at most [k] steps, [map f l] takes at most [k + 1] steps per
    element, plus one. *)
Theorem T_map_le {A B : Type} (f : A -> B) (T_f : A -> N) (k : N) (l : list A) :
  (forall x, T_f x <= k) -> T_map f T_f l <= (k + 1) * N.of_nat (length l) + 1.
Proof.
  intros Hf. induction l as [| x r IH].
  - rewrite T_map_nil. cbn [length]. lia.
  - rewrite T_map_cons. pose proof (Hf x) as Hx. cbn [length]. lia.
Qed.

(** [add_to_all n l] adds [n] to every element of [l].  [TimeFun] gives the closure
    [fun m => n + m] a companion that it derives from the closure's body:

      T_add_to_all n l = 1 + T_map (fun m => n + m) (fun m => 1 + Nat.T_add n m) l

    A call of the closure costs 1, plus [Nat.T_add n m] for the addition. *)
Definition add_to_all (n : nat) (l : list nat) : list nat := map (fun m => (n + m)%nat) l.

TimeFun add_to_all.

Lemma T_add_to_all_eq (n : nat) (l : list nat) :
  T_add_to_all n l = 1 + T_map (fun m => (n + m)%nat) (fun m => 1 + Nat.T_add n m) l.
Proof.
  reflexivity.
Qed.

(** Addition on [nat] recurses on its first argument, so a call of the closure takes at most
    [n + 2] steps, and [add_to_all n l] at most [n + 3] per element, plus two. *)
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
