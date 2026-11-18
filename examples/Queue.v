(** * A queue with an amortised bound

    The queue is a pair of lists: [push] adds to the back list, and [pop] takes from the front
    list.
    - When the front list is empty, [pop] first reverses the back list into the front.  One
      [pop] can take time linear in the size of the queue.
    - Each element is reversed at most once.  A sequence of operations from the empty queue
      costs at most 4 per operation ([queue_total]).
    - The proof uses a potential, the length of the back list.  Each [push] raises it by one,
      and that pays in advance for moving the element in a later reversal ([step_amortised]).

    For example, pushing 1, 2 and 3 and then popping costs 2 + 2 + 2 + 6 = 12 steps: the
    [pop] reverses three elements.  The bound for four operations is [4 * 4 = 16].

    Builds on: Time Tactics Amortised Std *)

From Stdlib Require Import List Lia NArith.
From Argent Require Import Time Tactics Amortised Std.
Import List.ListNotations.

(** * The queue *)

(** The front list and the back list.  The queue holds the front, followed by the reversed
    back. *)
Definition queue (A : Type) : Type := list A * list A.

Definition empty {A : Type} : queue A := ([], []).

Definition push {A : Type} (x : A) (q : queue A) : queue A :=
  let '(f, b) := q in (f, x :: b).

Definition pop {A : Type} (q : queue A) : option (A * queue A) :=
  let '(f, b) := q in
  match f with
  | x :: f' => Some (x, (f', b))
  | [] =>
    match rev_append b [] with
    | [] => None
    | x :: f' => Some (x, (f', []))
    end
  end.

(** An operation of a sequence, and its effect on the queue.  The amortised bound is about
    sequences, so [step] puts both operations behind one function. *)
Inductive op (A : Type) : Type :=
  | Push (x : A)
  | Pop.

Arguments Push {A} x.
Arguments Pop {A}.

Definition step {A : Type} (o : op A) (q : queue A) : queue A :=
  match o with
  | Push x => push x q
  | Pop =>
    match pop q with
    | Some (_, q') => q'
    | None => q
    end
  end.

(** [T_push] is the constant 1.  [Print T_pop] shows that a [pop] costs 1, plus the reversal
    when the front list is empty:

      T_pop =
      fun (A : Type) (q : queue A) =>
      (1 +
       (let (f, b) := q in
        match f with
        | [] => List.T_rev_append b []
        | _ :: _ => 0
        end))%N

    [T_step] adds 1 for the call of [step] itself. *)
TimeFun push pop step.

Example four_operations :
  total (@step nat) T_step [Push 1; Push 2; Push 3; Pop] empty = 12%N := eq_refl.

(** * The amortised bound *)

(** The potential: the length of the back list. *)
Definition back_length {A : Type} (q : queue A) : N := N.of_nat (length (snd q)).

Lemma rev_append_nil_length {A : Type} (b : list A) : length (rev_append b []) = length b.
Proof.
  rewrite rev_append_rev, app_nil_r. apply length_rev.
Qed.

(** Every operation costs at most 4 plus the drop in the potential: the actual time plus the
    new potential is at most 4 plus the old potential.  Each case below needs at most 3, so
    the bound 4 leaves some slack. *)
Theorem step_amortised {A : Type} :
  amortised (@step A) T_step (fun _ _ => 4%N) back_length (fun _ => True).
Proof.
  intros o [f b] _. split; [exact I |]. unfold back_length.
  destruct o as [x |]; time_unfold @T_step; cbn [step snd].
  - (* Push: 2 steps, and the back list grows by one. *)
    time_unfold @T_push. time_cbn. lia.
  - time_unfold @T_pop. destruct f as [| y f]; time_cbn.
    + (* Pop from an empty front: 2 steps, plus [length b + 1] for the reversal, and the
         back list becomes empty. *)
      pose proof (List.T_rev_append_le b []) as Hrev.
      pose proof (rev_append_nil_length b) as Hlen.
      destruct (rev_append b []) as [| y f]; time_cbn_all; lia.
    + (* Pop from a non-empty front: 2 steps, and the back list stays. *)
      lia.
Qed.

(** A sequence of [n] operations from the empty queue costs at most [4 * n]. *)
Theorem queue_total {A : Type} (os : list (op A)) :
  (total (@step A) T_step os empty <= 4 * N.of_nat (length os))%N.
Proof.
  (* [amortise] applies [amortised_uniform]: the total is at most [4 * length os] plus the
     potential of the empty queue, which is 0. *)
  amortise (fun _ : queue A => True) (@back_length A) (fun (_ : op A) (_ : queue A) => 4%N) 4%N.
  - (* Each operation is amortised. *)
    exact step_amortised.
  - (* The amortised cost of an operation is at most 4. *)
    intros _ _ _. lia.
  - (* The empty queue satisfies the invariant, which is [True]. *)
    exact I.
  - (* The empty queue has potential 0. *)
    unfold back_length. time_cbn. lia.
Qed.
