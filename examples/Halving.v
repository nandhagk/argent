(** * Well-founded recursion by halving

    This file defines two functions by [Fix] over [N.lt] and bounds their time with the
    potential lemma [Wf.T_Fix_le] of Std.  [log2] makes one recursive call on half of its
    argument, so its time is linear in the bit length of the argument.  [halves] makes two
    recursive calls on half of its argument, so its time is linear in the value of the
    argument.  Each step takes its proof of decrease from the equation of a convoy match.
    [Acc_intro_generator] unfolds the accessibility proof lazily, so both functions run under
    [vm_compute].

    For example, [log2 1000] is 9, and its time is at most
    [4 * N.of_nat (N.size_nat 1000) + 4].

    Builds on: Time Tactics Std *)

From Stdlib Require Import Lia PArith NArith.
From Argent Require Import Time Tactics Std.

(** Halving a positive number makes it smaller. *)
Lemma div2_lt (x : N) (q : positive) : x = N.pos q -> (N.div2 x < x)%N.
Proof.
  intros ->. destruct q; cbn [N.div2]; lia.
Qed.

(** * One recursive call *)

(** One step of the binary logarithm: 0 at 0 and 1, and one more than the logarithm of the half
    otherwise. *)
Definition log2_step (x : N) (rec : forall y : N, (y < x)%N -> nat) : nat :=
  match x as x' return x = x' -> nat with
  | N0 => fun _ => 0
  | N.pos q => fun E =>
    match q with
    | xH => 0
    | _ => S (rec (N.div2 x) (div2_lt x q E))
    end
  end eq_refl.

TimeFun log2_step.

Definition log2 (x : N) : nat :=
  Fix (Acc_intro_generator 64 N.lt_wf_0) (fun _ => nat) log2_step x.

TimeFun log2.

Example log2_runs : log2 1000 = 9.
Proof.
  vm_compute. reflexivity.
Qed.

(** The bit length of the half is one less. *)
Lemma size_nat_div2 (q : positive) : N.size_nat (N.div2 (N.pos q)) + 1 >= Pos.size_nat q.
Proof.
  destruct q; cbn [N.div2 N.size_nat Pos.size_nat]; lia.
Qed.

Local Open Scope N_scope.

(** Each step costs at most 3 besides its recursive call, which pays 4 per bit. *)
Theorem T_log2_le (x : N) : T_log2 x <= 4 * N.of_nat (N.size_nat x) + 4.
Proof.
  time_unfold @T_log2.
  enough (Hfix : Wf.T_Fix (Acc_intro_generator 64 N.lt_wf_0) (fun _ => nat) log2_step
    (fun x rec T_rec => T_log2_step x rec T_rec) x <= 4 * N.of_nat (N.size_nat x) + 2 + 1)
    by lia.
  apply (Wf.T_Fix_le (fun _ => nat) _ _ _ (fun x => 4 * N.of_nat (N.size_nat x) + 2)).
  intros y rec T_rec Hrec. time_unfold T_log2_step.
  destruct y as [| q]; cbn [N.size_nat]; [lia |].
  destruct q as [q | q |]; cbn [Pos.size_nat]; [| | lia];
    match goal with
    | |- context [T_rec ?z ?h] => pose proof (Hrec z h)
    end;
    pose proof (N.T_div2_le (N.pos q~1)); pose proof (N.T_div2_le (N.pos q~0));
    cbn [N.div2 N.size_nat] in *; lia.
Qed.

(** * Two recursive calls *)

Inductive tree : Type :=
  | Leaf
  | Node (l r : tree).

(** One step of [halves]: a leaf at 0 and 1, and a node with two copies of the tree of the half
    otherwise, each computed by its own recursive call. *)
Definition halves_step (x : N) (rec : forall y : N, (y < x)%N -> tree) : tree :=
  match x as x' return x = x' -> tree with
  | N0 => fun _ => Leaf
  | N.pos q => fun E =>
    match q with
    | xH => Leaf
    | _ => Node (rec (N.div2 x) (div2_lt x q E)) (rec (N.div2 x) (div2_lt x q E))
    end
  end eq_refl.

TimeFun halves_step.

Definition halves (x : N) : tree :=
  Fix (Acc_intro_generator 64 N.lt_wf_0) (fun _ => tree) halves_step x.

TimeFun halves.

(** The potential of [halves]: [8 x - 6] pays two calls on [x / 2] and a constant. *)
Definition halves_phi (x : N) : N :=
  match x with
  | N0 => 2
  | N.pos p => 8 * N.pos p - 6
  end.

Theorem T_halves_le (x : N) : T_halves x <= 8 * x + 4.
Proof.
  time_unfold @T_halves.
  enough (Hfix : Wf.T_Fix (Acc_intro_generator 64 N.lt_wf_0) (fun _ => tree) halves_step
    (fun x rec T_rec => T_halves_step x rec T_rec) x <= halves_phi x + 1).
  { destruct x as [| p]; cbn [halves_phi] in *; lia. }
  apply (Wf.T_Fix_le (fun _ => tree) _ _ _ halves_phi).
  intros y rec T_rec Hrec. time_unfold T_halves_step.
  destruct y as [| q]; cbn [halves_phi]; [lia |].
  destruct q as [q | q |]; [| | cbn; lia];
    match goal with
    | |- context [T_rec ?z ?h] => pose proof (Hrec z h)
    end;
    pose proof (N.T_div2_le (N.pos q~1)); pose proof (N.T_div2_le (N.pos q~0));
    cbn [N.div2 halves_phi] in *; lia.
Qed.
