(** * Tests of the complexity notation

    This file checks the notation of [ComplexityNotations] against the terms that it stands
    for.  Most examples state that a bound written in the notation equals the bound written
    with [bigO], [bigOmega], [bigTheta], [bigOmega_worst], [tight] or [bigO_amortised], and
    [same_term] proves it with [constr_eq], so a bound that parsed with another grouping or in
    another scope fails.  The groups check the twelve forms, the precedence of the notation, its
    scopes, its binders, the syntax around it that must still parse, and the example in the
    header of [Complexity].  Outside [LengthTests] the file opens no scope, so the scope tests
    read their statements in [nat_scope].

    For example, [precondition_takes_conjunction] checks that the precondition of
    [cost a b ∈ 𝑂(a) for (a, b) | below a b /\ a <> 0%N] is the whole conjunction.

    Builds on: Time Tactics Amortised Complexity Std *)

From Stdlib Require Import Lia NArith.
From Argent Require Import Time Tactics Amortised Complexity Std.
Import ComplexityNotations.

(** * Fixtures *)

(** A time of two arguments. *)
Definition cost (a b : N) : N := (a + b + 1)%N.

(** A precondition on two arguments. *)
Definition below (a b : N) : Prop := (b <= a)%N.

(** A time of one size of type [nat]. *)
Definition cost_nat (n : nat) : N := (N.of_nat n + 1)%N.

(** Prove [l = r] when [l] and [r] are the same term up to the names of bound variables. *)
Local Ltac same_term :=
  lazymatch goal with
  | |- ?l = ?r => constr_eq l r; reflexivity
  end.

(** * Forms *)

Module FormTests.

  (** The upper bound with a precondition is [bigO] on the inputs that satisfy it. *)
  Example upper :
    (cost a b ∈ 𝑂(a) for (a, b) | below a b) =
    bigO (fun '(a, b) => below a b) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The upper bound without a precondition is [bigO] on every input. *)
  Example upper_everywhere :
    (cost a b ∈ 𝑂(a) for (a, b)) =
    bigO (fun _ => True) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The lower bound with a precondition is [bigOmega]. *)
  Example lower :
    (cost a b ∈ Ω(a) for (a, b) | below a b) =
    bigOmega (fun '(a, b) => below a b) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The lower bound without a precondition is [bigOmega] on every input. *)
  Example lower_everywhere :
    (cost a b ∈ Ω(a) for (a, b)) =
    bigOmega (fun _ => True) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The tight bound with a precondition is [bigTheta]. *)
  Example tight_bound :
    (cost a b ∈ Θ(a) for (a, b) | below a b) =
    bigTheta (fun '(a, b) => below a b) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The tight bound without a precondition is [bigTheta] on every input. *)
  Example tight_bound_everywhere :
    (cost a b ∈ Θ(a) for (a, b)) =
    bigTheta (fun _ => True) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The worst-case lower bound with a precondition is [bigOmega_worst]. *)
  Example worst_lower :
    (cost a b ∈ Ω_worst(a) for (a, b) | below a b) =
    bigOmega_worst (fun '(a, b) => below a b) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The worst-case lower bound without a precondition is [bigOmega_worst] on every input. *)
  Example worst_lower_everywhere :
    (cost a b ∈ Ω_worst(a) for (a, b)) =
    bigOmega_worst (fun _ => True) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The worst-case tight bound with a precondition is [tight]. *)
  Example worst_tight :
    (cost a b ∈ Θ_worst(a) for (a, b) | below a b) =
    tight (fun '(a, b) => below a b) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The worst-case tight bound without a precondition is [tight] on every input. *)
  Example worst_tight_everywhere :
    (cost a b ∈ Θ_worst(a) for (a, b)) =
    tight (fun _ => True) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The amortised bound takes the potential before the operation, then the one after it. *)
  Example amortised_bound :
    (cost a b ∈ 𝑂(a) amortised a ↦ b for (a, b) | below a b) =
    bigO_amortised (fun '(a, b) => below a b) (fun '(a, _) => a) (fun '(a, b) => cost a b)
      (fun '(a, _) => a) (fun '(_, b) => b).
  Proof.
    same_term.
  Qed.

  (** The amortised bound without a precondition is [bigO_amortised] on every input. *)
  Example amortised_bound_everywhere :
    (cost a b ∈ 𝑂(a) amortised a ↦ b for (a, b)) =
    bigO_amortised (fun _ => True) (fun '(a, _) => a) (fun '(a, b) => cost a b)
      (fun '(a, _) => a) (fun '(_, b) => b).
  Proof.
    same_term.
  Qed.

End FormTests.

(** * Precedence *)

Module PrecedenceTests.

  (** A precondition extends to the end of the statement, so it takes a whole conjunction. *)
  Example precondition_takes_conjunction :
    (cost a b ∈ 𝑂(a) for (a, b) | below a b /\ a <> 0%N) =
    bigO (fun '(a, b) => below a b /\ a <> 0%N) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** A precondition also takes a following implication, so a bound before [->] needs
      parentheses. *)
  Example precondition_takes_implication :
    (cost a b ∈ 𝑂(a) for (a, b) | below a b -> a <> 0%N) =
    bigO (fun '(a, b) => below a b -> a <> 0%N) (fun '(a, _) => a) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** A bound in parentheses is the hypothesis of an implication. *)
  Example bound_in_parentheses :
    ((cost a b ∈ 𝑂(a) for (a, b) | below a b) -> True) =
    (bigO (fun '(a, b) => below a b) (fun '(a, _) => a) (fun '(a, b) => cost a b) -> True).
  Proof.
    same_term.
  Qed.

  (** Without a precondition a bound sits at level 70, so it is a conjunct as an equation is. *)
  Example bound_is_conjunct :
    (cost a b ∈ 𝑂(a + b) for (a, b) /\ True) =
    (bigO (fun _ => True) (fun '(a, b) => (a + b)%N) (fun '(a, b) => cost a b) /\ True).
  Proof.
    same_term.
  Qed.

  (** The time sits at level 69, so a sum of two times needs no parentheses. *)
  Example time_is_sum :
    (cost a b + cost b a ∈ Ω(a) for (a, b)) =
    bigOmega (fun _ => True) (fun '(a, _) => a) (fun '(a, b) => (cost a b + cost b a)%N).
  Proof.
    same_term.
  Qed.

  (** The potentials sit at level 69, so each of them can be a sum. *)
  Example potentials_are_sums :
    (cost a b ∈ 𝑂(a) amortised a + b ↦ b + 1 for (a, b)) =
    bigO_amortised (fun _ => True) (fun '(a, _) => a) (fun '(a, b) => cost a b)
      (fun '(a, b) => (a + b)%N) (fun '(_, b) => (b + 1)%N).
  Proof.
    same_term.
  Qed.

End PrecedenceTests.

(** * Scopes *)

Module ScopeTests.

  (** The measure is read in [N_scope], so [a * b + 1] is arithmetic of [N] without [%N]. *)
  Example measure_in_N :
    (cost a b ∈ Θ(a * b + 1) for (a, b)) =
    bigTheta (fun _ => True) (fun '(a, b) => (a * b + 1)%N) (fun '(a, b) => cost a b).
  Proof.
    same_term.
  Qed.

  (** The argument of [N.of_nat] stays in [nat_scope], so a size can be a sum of [nat]. *)
  Example size_in_nat :
    (cost_nat n ∈ 𝑂(N.of_nat (n + 1)) for n) =
    bigO (fun _ => True) (fun n => N.of_nat (n + 1)) (fun n => cost_nat n).
  Proof.
    same_term.
  Qed.

  (** The precondition is read in the scope of the statement, here the order of [nat]. *)
  Example precondition_in_nat :
    (cost_nat n ∈ 𝑂(N.of_nat n) for n | n <= 5) =
    bigO (fun n => n <= 5) (fun n => N.of_nat n) (fun n => cost_nat n).
  Proof.
    same_term.
  Qed.

End ScopeTests.

(** * Binders *)

Module BinderTests.

  (** A name binds the whole input. *)
  Example name :
    (cost_nat n ∈ 𝑂(N.of_nat n) for n) =
    bigO (fun _ => True) (fun n => N.of_nat n) (fun n => cost_nat n).
  Proof.
    same_term.
  Qed.

  (** A nested tuple pattern binds the components of a nested pair. *)
  Example nested_tuple :
    (cost a b ∈ 𝑂(a + c) for (a, (b, c))) =
    bigO (fun _ => True) (fun '(a, (_, c)) => (a + c)%N) (fun '(a, (b, _)) => cost a b).
  Proof.
    same_term.
  Qed.

  (** A variable bound outside the bound stays free in its time, measure and precondition. *)
  Example outer_variable :
    (forall k : N, cost a (b + k) ∈ 𝑂(a + k) for (a, b) | below b k) =
    (forall k : N,
       bigO (fun '(_, b) => below b k) (fun '(a, _) => (a + k)%N)
         (fun '(a, b) => cost a (b + k))).
  Proof.
    same_term.
  Qed.

End BinderTests.

(** * Syntax around the notation *)

Module NeighbourTests.

  (** A subset type keeps its bar. *)
  Example subset_type (s : {x : N | (x <= 3)%N}) : (proj1_sig s <= 3)%N.
  Proof.
    exact (proj2_sig s).
  Qed.

  (** A function on a quoted pair pattern keeps its quote. *)
  Example quoted_pattern : (fun '(x, y) => (x + y)%N) (1%N, 2%N) = 3%N.
  Proof.
    reflexivity.
  Qed.

  (** A [match] keeps its bars. *)
  Example match_bars (n : N) :
    match n with
    | 0%N => True
    | _ => True
    end.
  Proof.
    destruct n; exact I.
  Qed.

  (** [exists2] keeps its ampersand. *)
  Example exists2_ampersand : exists2 n : N, (n <= 3)%N & n = 3%N.
  Proof.
    exists 3%N; [lia | reflexivity].
  Qed.

  (** Argent's definition [amortised] keeps its name beside the keyword [amortised]. *)
  Example amortised_identifier (op : unit -> nat -> nat) (T A : unit -> nat -> N) :
    amortised op T A (fun _ => 0%N) (fun _ => True) ->
    amortised op T A (fun _ => 0%N) (fun _ => True).
  Proof.
    intros Hamort. exact Hamort.
  Qed.

  (** The constructor [O] of [nat] still takes a comment right after it, because the upper
      bound is written with the italic letter [𝑂]. *)
  Example comment_after_O : S O(* a comment right after the constructor *) = 1.
  Proof.
    reflexivity.
  Qed.

End NeighbourTests.

(** * The example in the header of Complexity *)

Module LengthTests.

  Local Open Scope N_scope.

  (** The time of [length] is the length of the list plus one. *)
  Lemma T_length_eq {A : Type} (l : list A) : Datatypes.T_length l = N.of_nat (length l) + 1.
  Proof.
    induction l as [| x l IH].
    - reflexivity.
    - time_unfold @Datatypes.T_length. time_cbn. lia.
  Qed.

  (** [length] runs in time Θ of the length of its list, with the constant 1 for both bounds. *)
  Example length_tight {A : Type} :
    Datatypes.T_length (A := A) l ∈ Θ(N.of_nat (length l)) for l.
  Proof.
    split; exists 1; intros l _; rewrite T_length_eq; lia.
  Qed.

End LengthTests.
