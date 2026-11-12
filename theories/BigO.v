(** * Big-O bounds

    This file defines [bigO P g T], which says that the time function [T] is bounded by a
    constant multiple of [g + 1] on every input that satisfies [P], and [tight P g T], which
    adds a matching lower bound on inputs of every size.  The input [x] is the tuple of all
    arguments, so the constant is uniform over all of them.  Times and sizes are in [N].

    For example, [bigO (fun _ => True) (fun l => N.of_nat (length l)) (fun l => T_length l)]
    holds with the constant 1, because [T_length l = N.of_nat (length l) + 1].

    Builds on: Stdlib Lia NArith *)

From Stdlib Require Import Lia NArith.

Local Open Scope N_scope.

(** * Definitions *)

(** [T] is at most [c * (g x + 1)] on the inputs that satisfy [P], for some constant [c]. *)
Definition bigO {X} (P : X -> Prop) (g T : X -> N) : Prop :=
  exists c, forall x, P x -> T x <= c * (g x + 1).

(** [T] is in O(g) on [P], and on inputs of every size [g] is at most a constant multiple of
    [T]. *)
Definition tight {X} (P : X -> Prop) (g T : X -> N) : Prop :=
  bigO P g T /\ exists c, forall n, exists x, P x /\ n <= g x /\ g x <= c * T x.

(** * Introduction and closure lemmas *)

Lemma bigO_intro {X} (P : X -> Prop) (g T : X -> N) c :
  (forall x, P x -> T x <= c * g x + c) -> bigO P g T.
Proof.
  intros Hle. exists c. intros x Hx. specialize (Hle x Hx). lia.
Qed.

Lemma bigO_le {X} (P : X -> Prop) (g T T2 : X -> N) :
  bigO P g T -> (forall x, P x -> T2 x <= T x) -> bigO P g T2.
Proof.
  intros [c Hc] Hle. exists c. intros x Hx. specialize (Hc x Hx). specialize (Hle x Hx). lia.
Qed.

Lemma bigO_mono {X} (P : X -> Prop) (g g2 T : X -> N) :
  bigO P g T -> (forall x, P x -> g x <= g2 x) -> bigO P g2 T.
Proof.
  intros [c Hc] Hle. exists c. intros x Hx. specialize (Hc x Hx). specialize (Hle x Hx). nia.
Qed.

Lemma bigO_add {X} (P : X -> Prop) (g1 g2 T1 T2 : X -> N) :
  bigO P g1 T1 -> bigO P g2 T2 ->
  bigO P (fun x => g1 x + g2 x) (fun x => T1 x + T2 x).
Proof.
  intros [c1 H1] [c2 H2]. exists (c1 + c2). intros x Hx.
  specialize (H1 x Hx). specialize (H2 x Hx). nia.
Qed.

Lemma bigO_trans {X} (P : X -> Prop) (g h T : X -> N) :
  bigO P g h -> bigO P h T -> bigO P g T.
Proof.
  intros [c1 H1] [c2 H2]. exists (c2 * c1 + c2). intros x Hx.
  specialize (H1 x Hx). specialize (H2 x Hx). nia.
Qed.

Lemma bigO_comp {X Y} (P : Y -> Prop) (f : X -> Y) (g T : Y -> N) :
  bigO P g T -> bigO (fun x => P (f x)) (fun x => g (f x)) (fun x => T (f x)).
Proof.
  intros [c Hc]. exists c. intros x Hx. exact (Hc (f x) Hx).
Qed.

(** A pointwise lower bound [g x <= c * T x] on inputs of unbounded size, together with an
    upper bound, gives [tight]. *)
Lemma tight_intro {X} (P : X -> Prop) (g T : X -> N) (c : N) (w : N -> X) :
  bigO P g T ->
  (forall n, P (w n)) -> (forall n, n <= g (w n)) -> (forall n, g (w n) <= c * T (w n)) ->
  tight P g T.
Proof.
  intros Hupper HP Hsize Hlower. split; [exact Hupper |].
  exists c. intros n. exists (w n). auto.
Qed.
