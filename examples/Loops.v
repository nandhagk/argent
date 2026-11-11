(** * Loops bounded by a potential

    This file uses the two loop combinators of Loop.v.  [countdown] iterates over an
    accessibility proof of [lt], which [Acc_intro_generator] unfolds lazily, so it runs under
    [vm_compute] and extracts with no fuel.  [count] iterates with fuel computed from the data.
    Both bounds come from the potential lemmas and do not depend on the proof or the fuel.

    For example, [countdown 3] steps from 3 to 0 and stops, so it costs at most [2 * 3 + 3].

    Builds on: Time Tactics Loop Std *)

From Stdlib Require Import List Lia Wf_nat.
From Argent Require Import Time Tactics Loop Std.
Import List.ListNotations.

(** * A loop over an accessibility proof *)

(** One step of the countdown: a smaller state, with the proof that it is smaller, or the
    result. *)
Definition count_step (n : nat) : {m : nat | m < n} + nat :=
  match n as k return {m : nat | m < k} + nat with
  | 0 => inr 0
  | S m => inl (exist _ m (PeanoNat.Nat.lt_succ_diag_r m))
  end.

TimeFun count_step.

Definition countdown (n : nat) : nat := loop lt count_step n (Acc_intro_generator 32 lt_wf n).

TimeFun countdown.

Example countdown_runs : countdown 1000 = 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** The countdown from [n] costs at most [2 * n + 3]: each step pays 2 from the potential. *)
Theorem T_countdown_le (n : nat) : T_countdown n <= 2 * n + 3.
Proof.
  time_unfold @T_countdown.
  match goal with
  | |- 1 + ?t <= _ => enough (Hloop : t <= 2 * n + 1 + 1) by lia
  end.
  loop_bound (fun _ : nat => True) (fun k : nat => 2 * k) 1.
  - intros [| k] s1 Hlt _ Hstep; cbn in Hstep; [discriminate |].
    injection Hstep as Hs1. subst s1. split; [exact I |]. time_simpl. lia.
  - intros s r _ _. time_simpl. lia.
  - exact I.
Qed.

(** * A loop with fuel computed from data *)

(** One step of counting the elements of a list: the count so far and the rest of the list. *)
Definition count_step_fuel (s : nat * list nat) : (nat * list nat) + nat :=
  match s with
  | (c, []) => inr c
  | (c, _ :: r) => inl (S c, r)
  end.

TimeFun count_step_fuel.

(** The fuel [length l + 1] suffices; the bound does not depend on it. *)
Definition count (l : list nat) : (nat * list nat) + nat :=
  loop_fuel count_step_fuel (length l + 1) (0, l).

TimeFun count.

Example count_runs : count [5; 6; 7] = inr 3 := eq_refl.

(** Counting a list costs at most [4 * length l + 5], including the computation of the fuel. *)
Theorem T_count_le (l : list nat) : T_count l <= 4 * length l + 5.
Proof.
  time_unfold @T_count. pose proof (Datatypes.T_length_le l) as Hlen.
  pose proof (Nat.T_add_le (length l) 1) as Hadd.
  match goal with
  | |- 1 + (_ + _ + ?t) <= _ => enough (Hloop : t <= 2 * length l + 1 + 1) by lia
  end.
  loop_bound (fun _ : nat * list nat => True)
    (fun s : nat * list nat => 2 * length (snd s)) 1.
  - intros [c [| x r]] s1 _ Hstep; cbn in Hstep; [discriminate |].
    injection Hstep as Hs1. subst s1. split; [exact I |]. time_simpl. cbn. lia.
  - intros s r _ _. time_simpl. lia.
  - exact I.
  - cbn. lia.
Qed.
