(** * Loops bounded by a potential

    A loop that doesn't recurse on a smaller piece of its input needs another argument for
    termination.  Loop.v offers two.  [loop] recurses on a proof that the state decreases (an
    accessibility proof): it needs no fuel, and it extracts to a plain recursive function.
    [loop_fuel] takes a [nat] bound on the number of iterations, called fuel.  Either way, the
    time comes from a potential [Phi] on the states: when every step that continues makes
    [Phi] drop by more than the step costs, the loop costs at most [Phi] of the first state,
    plus the cost of the last step, plus one.  The bound depends neither on the proof nor on
    the fuel.

    For example, [countdown 3] steps from 3 to 2, 1 and 0, and stops there.  With the
    potential [2 * n], its time is at most [2 * 3 + 3].

    Builds on: Time Tactics Loop Std *)

From Stdlib Require Import List Lia NArith Wf_nat.
From Argent Require Import Time Tactics Loop Std.
Import List.ListNotations.

(** * A loop over an accessibility proof *)

(** One step of the countdown.  From [S m] it continues with [m], together with a proof that
    [m < S m].  At 0 it stops with the result 0. *)
Definition count_step (n : nat) : {m : nat | m < n} + nat :=
  match n as k return {m : nat | m < k} + nat with
  | 0 => inr 0
  | S m => inl (exist _ m (PeanoNat.Nat.lt_succ_diag_r m))
  end.

TimeFun count_step.

(** [lt_wf] proves that [lt] is well founded, but its proof ends in [Qed], so it never
    reduces to a constructor and [loop] can't compute with it.  [Acc_intro_generator 32 lt_wf]
    puts [2 ^ 32] constructors in front of it, built lazily, so any countdown that ends in
    fewer than [2 ^ 32] steps runs under [vm_compute]. *)
Definition countdown (n : nat) : nat := loop lt count_step n (Acc_intro_generator 32 lt_wf n).

TimeFun countdown.

Example countdown_runs : countdown 1000 = 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** [T_countdown] calls the time function of [loop], with [T_count_step] as the companion of
    the step function. *)
Lemma T_countdown_unfold (n : nat) :
  T_countdown n =
  (1 + T_loop lt count_step T_count_step n (Acc_intro_generator 32 lt_wf n))%N.
Proof.
  reflexivity.
Qed.

(** The countdown from [n] costs at most [2 * n + 3].  The potential [2 * k] drops by 2 at
    each step, which pays for the step and for its recursive call. *)
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

(** * A loop with fuel *)

(** One step of counting the elements of a list.  The state is the count so far and the rest
    of the list. *)
Definition count_step_fuel (s : nat * list nat) : (nat * list nat) + nat :=
  match s with
  | (c, []) => inr c
  | (c, _ :: r) => inl (S c, r)
  end.

TimeFun count_step_fuel.

(** Each step removes one element, so the fuel [length l + 1] is enough.  The bound below
    holds for any fuel, though, because a loop that runs out of fuel only stops earlier. *)
Definition count (l : list nat) : (nat * list nat) + nat :=
  loop_fuel count_step_fuel (length l + 1) (0, l).

TimeFun count.

Example count_runs : count [5; 6; 7] = inr 3 := eq_refl.

(** [T_count l] is 1, plus the cost of computing the fuel, plus the cost of the loop. *)
Lemma T_count_unfold (l : list nat) :
  T_count l =
  (1 + (Datatypes.T_length l + Nat.T_add (length l) 1
        + T_loop_fuel count_step_fuel T_count_step_fuel (length l + 1) (0%nat, l)))%N.
Proof.
  reflexivity.
Qed.

(** Counting a list costs at most [4 * length l + 5], including the computation of the fuel. *)
Theorem T_count_le (l : list nat) : (T_count l <= 4 * N.of_nat (length l) + 5)%N.
Proof.
  rewrite T_count_unfold.
  (* Computing the fuel costs at most [length l + 1] for [length], and as much for [+ 1]. *)
  pose proof (Datatypes.T_length_le l) as Hlength.
  pose proof (Nat.T_add_le (length l) 1) as Hadd.
  (* [T_loop_fuel_le] bounds the loop by [Phi (0, l) + Tstop + 1], with
     [Phi s = 2 * length (snd s)] and [Tstop = 1]. *)
  enough (Hloop : (T_loop_fuel count_step_fuel T_count_step_fuel (length l + 1) (0%nat, l)
                   <= 2 * N.of_nat (length l) + 1 + 1)%N) by lia.
  apply (T_loop_fuel_le count_step_fuel T_count_step_fuel (fun _ => True)
    (fun s => 2 * N.of_nat (length (snd s)))%N 1%N).
  - (* A step that continues removes one element: it costs 1, and the potential drops by 2. *)
    intros [c [| x r]] s1 _ Hstep; cbn in Hstep; [discriminate |].
    injection Hstep as <-. split; [exact I |]. time_simpl. time_cbn. lia.
  - (* The step on an empty list stops, and costs 1. *)
    intros s r _ _. time_simpl. lia.
  - (* The invariant is [True]. *)
    exact I.
Qed.
