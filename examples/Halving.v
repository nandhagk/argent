(** * Well-founded recursion by halving

    [log2] and [halves] recurse on half of their argument, which is not a structural
    subterm, so they are written with [Fix] over [N.lt].  [TimeFun] derives their time
    functions like any others, and [Wf.T_Fix_le] bounds them with a potential [Phi]: when each
    step, given recursive calls that cost at most [Phi y + 1], costs at most [Phi x] including
    its own call, the whole recursion from [x] costs at most [Phi x + 1].

    [log2] makes one recursive call on half of its argument, so its time is linear in the bit
    length of the argument.  [halves] makes two, so its time is linear in the value of the
    argument.

    For example, [log2 1000] is 9, and its time is at most
    [4 * N.of_nat (N.size_nat 1000) + 4 = 44].

    Builds on: Time Tactics Std *)

From Stdlib Require Import Lia PArith NArith.
From Argent Require Import Time Tactics Std.

(** Halving a positive number makes it smaller. *)
Lemma div2_lt (x : N) (q : positive) : x = N.pos q -> (N.div2 x < x)%N.
Proof.
  intros ->. destruct q; cbn [N.div2]; lia.
Qed.

(** * One recursive call *)

(** One step of the binary logarithm: 0 at 0 and at 1, and one more than the logarithm of the
    half otherwise.  The recursive call [rec] needs a proof that the half is smaller.  That
    proof is [div2_lt x q E], where [E : x = N.pos q] comes from the match itself: the clause
    [return x = x' -> nat] makes each branch take an equation for its own case, and
    [eq_refl] at the end provides it.  This is called a convoy match. *)
Definition log2_step (x : N) (rec : forall y : N, (y < x)%N -> nat) : nat :=
  match x as x' return x = x' -> nat with
  | N0 => fun _ => 0
  | N.pos q => fun E =>
    match q with
    | xH => 0
    | _ => S (rec (N.div2 x) (div2_lt x q E))
    end
  end eq_refl.

(** [T_log2_step x rec T_rec] has an extra argument [T_rec], the companion of [rec]: a
    recursive call [rec y h] costs [T_rec y h].  Proofs cost nothing. *)
TimeFun log2_step.

(** [N.lt_wf_0] ends in [Qed], so it never reduces to a constructor.
    [Acc_intro_generator 64] puts [2 ^ 64] constructors in front of it, built lazily, so
    that [log2] runs under [vm_compute]. *)
Definition log2 (x : N) : nat :=
  Fix (Acc_intro_generator 64 N.lt_wf_0) (fun _ => nat) log2_step x.

TimeFun log2.

Example log2_runs : log2 1000 = 9.
Proof.
  vm_compute. reflexivity.
Qed.

Local Open Scope N_scope.

(** [log2] takes at most 4 steps per bit of its argument, plus 4. *)
Theorem T_log2_le (x : N) : T_log2 x <= 4 * N.of_nat (N.size_nat x) + 4.
Proof.
  time_unfold @T_log2.
  (* [Wf.T_Fix_le] bounds the recursion by [Phi x + 1], with [Phi x = 4 * size x + 2]. *)
  enough (Hfix : Wf.T_Fix (Acc_intro_generator 64 N.lt_wf_0) (fun _ => nat) log2_step
    (fun x rec T_rec => T_log2_step x rec T_rec) x <= 4 * N.of_nat (N.size_nat x) + 2 + 1)
    by lia.
  apply (Wf.T_Fix_le (fun _ => nat) _ _ _ (fun x => 4 * N.of_nat (N.size_nat x) + 2)).
  intros y rec T_rec Hrec. time_unfold T_log2_step.
  destruct y as [| q].
  - (* At 0 the step stops at once. *)
    cbn [N.size_nat]. lia.
  - (* At [N.pos q], the step halves its argument and calls [rec] on the half, unless
       [q = 1].  The half has one bit fewer, so the call costs [4 * (size - 1) + 3]. *)
    pose proof (Hrec (N.div2 (N.pos q)) (div2_lt (N.pos q) q eq_refl)) as Hhalf.
    pose proof (N.T_div2_le (N.pos q)) as Hdiv2.
    destruct q as [q | q |]; cbn [N.div2 N.size_nat Pos.size_nat] in *; lia.
Qed.

(** * Two recursive calls *)

Inductive tree : Type :=
  | Leaf
  | Node (l r : tree).

(** One step of [halves]: a leaf at 0 and at 1, and otherwise a node whose two children are
    the trees of the half, each computed by its own recursive call. *)
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

(** The potential of [halves].  [8 * x - 6] pays for two calls on [x / 2], each costing at
    most [8 * (x / 2) - 6 + 1], plus the step itself. *)
Definition halves_phi (x : N) : N :=
  match x with
  | N0 => 2
  | N.pos p => 8 * N.pos p - 6
  end.

(** [halves x] takes time linear in the value of [x]. *)
Theorem T_halves_le (x : N) : T_halves x <= 8 * x + 4.
Proof.
  time_unfold @T_halves.
  (* [Wf.T_Fix_le] bounds the recursion by [halves_phi x + 1]. *)
  enough (Hfix : Wf.T_Fix (Acc_intro_generator 64 N.lt_wf_0) (fun _ => tree) halves_step
    (fun x rec T_rec => T_halves_step x rec T_rec) x <= halves_phi x + 1).
  { destruct x as [| p]; cbn [halves_phi] in *; lia. }
  apply (Wf.T_Fix_le (fun _ => tree) _ _ _ halves_phi).
  intros y rec T_rec Hrec. time_unfold T_halves_step.
  destruct y as [| q].
  - (* At 0 the step stops at once. *)
    cbn [halves_phi]. lia.
  - (* At [N.pos q], the step makes two equal recursive calls on the half, unless [q = 1]. *)
    pose proof (Hrec (N.div2 (N.pos q)) (div2_lt (N.pos q) q eq_refl)) as Hhalf.
    pose proof (N.T_div2_le (N.pos q)) as Hdiv2.
    destruct q as [q | q |]; cbn [N.div2 halves_phi] in *; lia.
Qed.
