(** * The two-list functional queue

    This file defines a queue as a front list and a back list.  [push] adds to the back, and
    [pop] takes from the front, reversing the back into the front when the front is empty.  A
    single [pop] can cost time linear in the queue, but with the potential "length of the back
    list" every operation has a constant amortised cost, so any sequence of [n] operations
    from the empty queue costs at most [4 * n].

    For example, pushing 1, 2 and 3 and then popping costs one reversal of three elements,
    which the three pushes paid for in advance.

    Builds on: Time Tactics Amortised Std *)

From Stdlib Require Import List Lia.
From Argent Require Import Time Tactics Amortised Std.
Import List.ListNotations.

(** * The queue *)

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

(** An operation of a sequence, and its effect on the queue. *)
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

TimeFun push pop step.

(** * Amortised bound *)

(** The potential: every element of the back list has paid for its share of a reversal. *)
Definition back_length {A : Type} (q : queue A) : nat := length (snd q).

Lemma rev_append_nil_length {A : Type} (b : list A) : length (rev_append b []) = length b.
Proof.
  rewrite rev_append_rev, app_nil_r. apply length_rev.
Qed.

(** Every operation costs at most 4 plus the decrease of the potential. *)
Theorem step_amortised {A : Type} :
  amortised (@step A) T_step (fun _ _ => 4) back_length (fun _ => True).
Proof.
  intros o [f b] _. split; [exact I |].
  destruct o as [x |]; time_unfold @T_step; cbn [step back_length snd].
  - time_unfold @T_push. cbn. lia.
  - time_unfold @T_pop. destruct f as [| y f]; cbn.
    + pose proof (List.T_rev_append_le b []) as Hrev.
      pose proof (rev_append_nil_length b) as Hlen.
      destruct (rev_append b []) as [| y f]; cbn in *; lia.
    + lia.
Qed.

(** A sequence of [n] operations from the empty queue costs at most [4 * n]. *)
Theorem queue_total {A : Type} (os : list (op A)) :
  total (@step A) T_step os empty <= 4 * length os.
Proof.
  amortise (fun _ : queue A => True) (@back_length A) (fun (_ : op A) (_ : queue A) => 4) 4.
  - exact step_amortised.
  - intros _ _ _. lia.
  - exact I.
  - cbn. lia.
Qed.
