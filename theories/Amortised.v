(** * Amortised bounds

    This file proves Tarjan's potential method for a sequence of operations.  An operation [o]
    maps a state [s] to [op o s] at cost [T o s].  When every operation satisfies
    [T o s + Phi (op o s) <= A o s + Phi s] for a potential [Phi], the total cost of a
    sequence is at most its total amortised cost plus the initial potential.

    For example, a queue built from two lists has [Phi] equal to the length of its back list
    and an amortised cost of a constant per operation, so [n] operations from the empty queue
    cost at most a constant times [n].

    The bounds hold along one sequence of versions.  They say nothing about a branching history
    in which one version is used several times.

    Builds on: Stdlib Lia *)

From Stdlib Require Import List Lia.
Import List.ListNotations.

Section Amortised.

Context {S O : Type} (op : O -> S -> S) (T A : O -> S -> nat) (Phi : S -> nat)
  (Inv : S -> Prop).

(** The state after the operations [os]. *)
Fixpoint run (os : list O) (s : S) : S :=
  match os with
  | [] => s
  | o :: r => run r (op o s)
  end.

(** The actual cost of the operations [os]. *)
Fixpoint total (os : list O) (s : S) : nat :=
  match os with
  | [] => 0
  | o :: r => T o s + total r (op o s)
  end.

(** The amortised cost of the operations [os]. *)
Fixpoint budget (os : list O) (s : S) : nat :=
  match os with
  | [] => 0
  | o :: r => A o s + budget r (op o s)
  end.

(** Every operation keeps the invariant and pays its actual cost and the change of potential
    from its amortised cost. *)
Definition amortised : Prop :=
  forall o s, Inv s -> Inv (op o s) /\ T o s + Phi (op o s) <= A o s + Phi s.

(** Along a sequence, the actual cost plus the final potential is at most the amortised cost
    plus the initial potential. *)
Theorem amortised_run :
  amortised -> forall os s, Inv s -> total os s + Phi (run os s) <= budget os s + Phi s.
Proof.
  intros Hamort os. induction os as [| o r IH]; intros s Hs; cbn [total run budget].
  - lia.
  - destruct (Hamort o s Hs) as [Hinv Hstep]. specialize (IH (op o s) Hinv). lia.
Qed.

(** With an amortised cost of at most [k] per operation, a sequence of [n] operations costs at
    most [k * n] plus the initial potential. *)
Theorem amortised_uniform (k : nat) :
  amortised -> (forall o s, Inv s -> A o s <= k) ->
  forall os s, Inv s -> total os s <= k * length os + Phi s.
Proof.
  intros Hamort Hcap.
  assert (Hbudget : forall os s, Inv s -> budget os s <= k * length os).
  { intros os. induction os as [| o r IH]; intros s Hs; cbn [budget length].
    - lia.
    - destruct (Hamort o s Hs) as [Hinv _]. specialize (IH (op o s) Hinv).
      specialize (Hcap o s Hs). lia. }
  intros os s Hs. pose proof (amortised_run Hamort os s Hs) as Hrun.
  specialize (Hbudget os s Hs). lia.
Qed.

End Amortised.
