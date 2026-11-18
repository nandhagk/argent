(** * Amortised bounds

    The potential method of Tarjan, for operations that are expensive now and then but cheap
    on average over any sequence of them.
    - An operation [o] maps a state [s] to [op o s] and costs [T o s].
    - Choose a potential [Phi] on states and an amortised cost [A], and show that every
      operation satisfies

        T o s + Phi (op o s) <= A o s + Phi s

    - Then a sequence of operations costs at most the sum of its amortised costs, plus the
      potential of the first state ([amortised_run], [amortised_uniform]).
    - The bounds hold along one sequence of states, each used once.  They say nothing about a
      history that uses one state several times, because repeating an expensive operation on
      the same state is not paid for.

    For example, a queue made of two lists, with [Phi] the length of the back list, has an
    amortised cost of a constant per operation.  So [n] operations from the empty queue cost
    at most a constant times [n].

    Builds on: Stdlib Lia NArith *)

From Stdlib Require Import List Lia NArith.
Import List.ListNotations.

Local Open Scope N_scope.

Section Amortised.

(** The operations [op], their costs [T], their amortised costs [A], the potential [Phi], and
    the invariant [Inv] that the states keep. *)
Context {S O : Type} (op : O -> S -> S) (T A : O -> S -> N) (Phi : S -> N)
  (Inv : S -> Prop).

(** The state after the operations [os]. *)
Fixpoint run (os : list O) (s : S) : S :=
  match os with
  | [] => s
  | o :: r => run r (op o s)
  end.

(** The actual cost of the operations [os]. *)
Fixpoint total (os : list O) (s : S) : N :=
  match os with
  | [] => 0
  | o :: r => T o s + total r (op o s)
  end.

(** The amortised cost of the operations [os]. *)
Fixpoint budget (os : list O) (s : S) : N :=
  match os with
  | [] => 0
  | o :: r => A o s + budget r (op o s)
  end.

(** Every operation keeps the invariant [Inv], and its cost plus the potential that it leaves
    is at most its amortised cost plus the potential that it found. *)
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
Theorem amortised_uniform (k : N) :
  amortised -> (forall o s, Inv s -> A o s <= k) ->
  forall os s, Inv s -> total os s <= k * N.of_nat (length os) + Phi s.
Proof.
  intros Hamort Hcap.
  assert (Hbudget : forall os s, Inv s -> budget os s <= k * N.of_nat (length os)).
  { intros os. induction os as [| o r IH]; intros s Hs; cbn [budget length].
    - lia.
    - destruct (Hamort o s Hs) as [Hinv _]. specialize (IH (op o s) Hinv).
      specialize (Hcap o s Hs). lia. }
  intros os s Hs. pose proof (amortised_run Hamort os s Hs) as Hrun.
  specialize (Hbudget os s Hs). lia.
Qed.

End Amortised.
