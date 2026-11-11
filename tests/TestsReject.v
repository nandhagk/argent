(** * Rejection tests

    This file checks that [TimeFun] rejects every definition whose cost it cannot account for,
    each with its own error code.  Every case has a [Fail TimeFun] and a [TimeFunFails] that
    names the expected code.

    For example, [Some (fun x => x)] stores a closure in data and is rejected with
    [E_CLOSURE_DATA].

    Builds on: Time Std *)

From Stdlib Require Import List Wf_nat.
From Argent Require Import Time Std.
Import List.ListNotations.

(** * Closures in data *)

Definition closure_in_option : option (nat -> nat) := Some (fun x => x).

Fail TimeFun closure_in_option.

TimeFunFails "E_CLOSURE_DATA" closure_in_option.

(** A function value passed where a polymorphic constructor expects data. *)
Definition closure_in_list (g : nat -> nat) : list (nat -> nat) := [g].

Fail TimeFun closure_in_list.

TimeFunFails "E_CLOSURE_DATA" closure_in_list.

(** * Calls without a time function *)

Definition untimed (n : nat) : nat := S n.

Definition calls_untimed (n : nat) : nat := untimed n.

Fail TimeFun calls_untimed.

TimeFunFails "E_NO_TIME" calls_untimed.

(** A closure taken out of data has no companion, so it cannot be called. *)
Definition calls_stored (l : list (nat -> nat)) : nat :=
  match l with
  | [] => 0
  | f :: _ => f 0
  end.

Fail TimeFun calls_stored.

TimeFunFails "E_NO_TIME" calls_stored.

(** * Over-application *)

Definition poly_id {A : Type} (x : A) : A := x.

TimeFun poly_id.

(** The result of a polymorphic function cannot be called, since its time function has no
    companion for it. *)
Definition over_applied (n : nat) : nat := @poly_id (nat -> nat) S n.

Fail TimeFun over_applied.

TimeFunFails "E_OVERAPP" over_applied.

(** * A match that returns a function *)

Definition match_fn (b : bool) (n : nat) : nat := (match b with true => S | false => pred end) n.

Fail TimeFun match_fn.

TimeFunFails "E_MATCH_FN" match_fn.

(** * A closure where a polymorphic callee expects data *)

Definition apply_zero {A : Type} (f : nat -> A) : A := f 0.

TimeFun apply_zero.

Definition closure_result : nat -> nat := apply_zero (fun x y => x + y).

Fail TimeFun closure_result.

TimeFunFails "E_CLOSURE" closure_result.

(** * Well-founded recursion *)

Definition by_fix (n : nat) : nat :=
  Fix (well_founded_ltof nat (fun k => k)) (fun _ => nat) (fun _ _ => 0) n.

Fail TimeFun by_fix.

TimeFunFails "E_WF" by_fix.

(** * Opaque constants *)

Definition opaque_succ (n : nat) : nat.
Proof.
  exact (S n).
Qed.

Fail TimeFun opaque_succ.

TimeFunFails "E_OPAQUE" opaque_succ.

Definition calls_opaque (n : nat) : nat := opaque_succ n.

Fail TimeFun calls_opaque.

TimeFunFails "E_OPAQUE" calls_opaque.

(** * Section variables *)

Section WithVariables.

Variable g : nat -> nat.

Variable k : nat.

Definition uses_function_variable (n : nat) : nat := g n.

Definition uses_data_variable (n : nat) : nat := n + k.

Fail TimeFun uses_function_variable.

TimeFunFails "E_SECTION" uses_function_variable.

Fail TimeFun uses_data_variable.

TimeFunFails "E_SECTION" uses_data_variable.

End WithVariables.

(** * Unsupported terms *)

Definition let_fn_position (l : list nat) : list nat := map (let g := S in g) l.

Fail TimeFun let_fn_position.

TimeFunFails "E_TERM" let_fn_position.

(** Elpi cannot read a cofixpoint, so a definition that contains one is rejected before
    translation. *)
CoInductive stream : Type :=
  | Cons (x : nat) (rest : stream).

Definition head_of_ones (n : nat) : nat :=
  match (cofix ones (k : nat) : stream := Cons k (ones k)) n with
  | Cons x _ => x
  end.

Fail TimeFun head_of_ones.

(** * Commands used on the wrong objects *)

TimeFunFails "E_NOT_CODE" nat.

TimeFunFails "E_NOT_CODE" le_n.

(** A constant of another library needs a module that mirrors its path. *)
TimeFunFails "E_PLACE" Nat.sub.

(** A time function is derived once. *)
TimeFunFails "E_TIMED" poly_id.

Fail TimeFun poly_id.

(** * A hand-written sibling time function *)

(** [TimeFun] finds the time function of a callee by its name beside the callee and does not
    check that it was derived, so it accepts the hand-written [T_cheat] below.  [TimeCheck] and
    [TimeAudit] re-derive the time function and reject it. *)
Definition T_cheat (n : nat) : nat := 0.

Definition cheat (n : nat) : nat := n * n * n.

Definition use_cheat (n : nat) : nat := cheat n + 1.

TimeFun use_cheat.

Fail TimeCheck cheat.

Fail TimeAudit use_cheat.
