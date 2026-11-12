(** * Tactic tests

    This file checks the tactics on small goals: [time_unfold] unfolds one step and refolds
    recursive calls, [time_simpl] replaces constant time functions by their value, [time_pose]
    poses registered, sibling and conditional bounds, and [time_step] combines them.

    For example, [time_pose] on a goal that mentions [T_twice 3] adds the registered bound
    [twice_bound 3].

    Builds on: Time Tactics Std *)

From Stdlib Require Import List Lia NArith.
From Argent Require Import Time Tactics Std.
Import List.ListNotations.

Definition twice (n : nat) : nat := n + n.

TimeFun twice.

(** A bound registered under a name that the sibling rule does not find. *)
Lemma twice_bound (n : nat) : (T_twice n <= N.of_nat n + 2)%N.
Proof.
  time_step.
Qed.

TimeBound twice_bound.

(** [time_pose] adds the registered bound of every time function in the goal. *)
Example pose_registered (n : nat) : (T_twice n + T_twice 3 <= N.of_nat n + 7)%N.
Proof.
  time_pose. lia.
Qed.

(** A conditional bound, whose premise [time_pose] discharges with [lia]. *)
Lemma twice_small (n : nat) : n <= 5 -> (T_twice n <= 7)%N.
Proof.
  intros Hn. pose proof (twice_bound n). lia.
Qed.

TimeBound twice_small.

Example pose_conditional : (T_twice 4 <= 7)%N.
Proof.
  time_pose. assumption.
Qed.

(** [time_simpl] unfolds the time functions whose value is a numeral. *)
Example simpl_constant (a b : bool) : (Datatypes.T_andb a b + Datatypes.T_negb a = 2)%N.
Proof.
  time_simpl. reflexivity.
Qed.

(** [time_unfold] unfolds one step and refolds the recursive call. *)
Example unfold_refolds (x : nat) (l : list nat) :
  Datatypes.T_length (x :: l) = (1 + Datatypes.T_length l)%N.
Proof.
  time_unfold @Datatypes.T_length. reflexivity.
Qed.

(** [time_unfold] leaves a recursive time function whose structural argument is not a
    constructor, since conversion cannot unfold it. *)
Example unfold_stuck (l : list nat) : Datatypes.T_length l = Datatypes.T_length l.
Proof.
  time_unfold @Datatypes.T_length. reflexivity.
Qed.

(** [time_step] on a goal with no time function fails with a message. *)
Example step_needs_time_function : (1 <= 2)%N.
Proof.
  Fail time_step. lia.
Qed.

(** [time_step f] names the function instead of its time function. *)
Example step_by_name (l m : list nat) : (Datatypes.T_app l m <= N.of_nat (length l) + 1)%N.
Proof.
  induction l as [| x l IH]; time_step app.
Qed.
