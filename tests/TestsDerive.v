(** * Derivation tests

    This file tests the features of [TimeFun] beyond plain structural recursion: mutual and
    local fixpoints, lets of functions, beta-redexes, partial application and eta-expansion,
    [TimeUnfold] on an identity monad, nested inductive types, universe polymorphism, implicit
    arguments, closed constants, [TimePrim], [TimeCheck] and [TimeAudit].  Each [Example] is
    checked by [vm_compute] or by conversion.

    For example, [redex_once] checks that the argument of [(fun x => x + x) (expensive n)] is
    charged once.

    Builds on: Time Std *)

From Stdlib Require Import List PArith.
From Argent Require Import Time Std.
Import List.ListNotations.

(** * A cost that is easy to recognise *)

Definition expensive (n : nat) : nat := n * n.

TimeFun expensive.

Example expensive_cost : T_expensive 3 = 17 := eq_refl.

(** * Beta-redexes, partial application and eta-expansion *)

(** A beta-redex is a let: the argument is evaluated once, even when it is used twice. *)
Definition redex (n : nat) : nat := (fun x => x + x) (expensive n).

TimeFun redex.

Example redex_once : T_redex 3 = 1 + T_expensive 3 + Nat.T_add 9 9 := eq_refl.

(** An unused argument of a redex is still evaluated. *)
Definition dropped (n : nat) : nat := (fun _ : nat => 0) (expensive n).

TimeFun dropped.

Example dropped_paid : T_dropped 3 = 1 + T_expensive 3 := eq_refl.

(** A partial application evaluates its argument once, when the closure is created. *)
Definition partial (n : nat) (l : list nat) : list nat := map (Nat.add (expensive n)) l.

TimeFun partial.

Example partial_once :
  T_partial 3 [1; 2; 3] = 1 + T_expensive 3 + (1 + 3 * (Nat.T_add 9 0 + 1)) := eq_refl.

(** An eta-expanded closure evaluates the argument at every call. *)
Definition eta_expanded (n : nat) (l : list nat) : list nat := map (fun x => expensive n + x) l.

TimeFun eta_expanded.

Example eta_each_call :
  T_eta_expanded 3 [1; 2; 3] = 1 + (1 + 3 * (1 + T_expensive 3 + Nat.T_add 9 0 + 1)) :=
  eq_refl.

(** A closure passed to a higher-order function is charged at each call, plus one for the call
    itself. *)
Definition sum (l : list nat) : nat := fold_left (fun acc x => acc + x) l 0.

TimeFun sum.

Example sum_cost : T_sum [1; 2; 3] = 15 := eq_refl.

(** * Lets and local fixpoints *)

(** A let of a function gets a companion time function. *)
Definition let_fun (n : nat) : nat := let g := fun x => x + n in g n + g 1.

TimeFun let_fun.

Example let_fun_cost : T_let_fun 2 = 1 + (1 + 3) + (1 + 2) + Nat.T_add 4 3 := eq_refl.

(** A local fixpoint gets a local time function. *)
Definition sum_to (n : nat) : nat :=
  (fix go (k acc : nat) := match k with 0 => acc | S k' => go k' (acc + k) end) n 0.

TimeFun sum_to.

Example sum_to_cost : T_sum_to 3 = 1 + (1 + 1) + (1 + 4) + (1 + 6) + 1 := eq_refl.

(** A local mutual fixpoint gets a local mutual time function. *)
Definition even_by_odd (n : nat) : bool :=
  (fix ev (k : nat) : bool := match k with 0 => true | S m => od m end
   with od (k : nat) : bool := match k with 0 => false | S m => ev m end
   for ev) n.

TimeFun even_by_odd.

Example even_by_odd_cost : T_even_by_odd 4 = 6 := eq_refl.

(** * Mutual fixpoints *)

(** [Pos.add] and [Pos.add_carry] form one block, and [Std] derives both. *)
Example pos_add_cost : Pos.T_add 7 1 = 3 := eq_refl.

Fixpoint even (n : nat) : bool :=
  match n with
  | 0 => true
  | S m => odd m
  end
with odd (n : nat) : bool :=
  match n with
  | 0 => false
  | S m => even m
  end.

TimeFun odd.

Example even_derived_with_odd : T_even 3 = 4 /\ T_odd 3 = 4 := conj eq_refl eq_refl.

(** * The identity monad *)

Definition M (A : Type) : Type := A.

Definition ret {A : Type} (a : A) : M A := a.

Definition bind {A B : Type} (m : M A) (f : A -> M B) : M B := f m.

TimeUnfold ret bind.

Definition monadic (n : nat) : M nat :=
  bind (ret (expensive n)) (fun x => bind (ret (x + 1)) (fun y => ret (y + x))).

Definition direct (n : nat) : nat := let x := expensive n in let y := x + 1 in y + x.

TimeFun monadic direct.

(** Under [TimeUnfold], [bind m (fun x => k)] costs what [let x := m in k] costs. *)
Example monadic_is_direct : T_monadic = T_direct := eq_refl.

(** * Nested inductive types *)

#[warnings="-register-all"]
Inductive tree : Type :=
  | Node (n : nat) (ts : list tree).

(** Recursion through [map] of the function being defined. *)
Fixpoint size (t : tree) : nat :=
  match t with
  | Node _ ts => 1 + fold_right Nat.add 0 (map size ts)
  end.

TimeFun size.

(** Recursion through a local fixpoint over the list of subtrees. *)
Fixpoint size_local (t : tree) : nat :=
  match t with
  | Node _ ts =>
    S ((fix go (l : list tree) : nat :=
          match l with
          | [] => 0
          | u :: r => size_local u + go r
          end) ts)
  end.

TimeFun size_local.

Definition sample : tree := Node 0 [Node 1 []; Node 2 [Node 3 []]].

Example size_cost : T_size sample = 33 := eq_refl.

Example size_local_cost : T_size_local sample = 18 := eq_refl.

(** * Closed constants and primitive costs *)

(** A closed constant is evaluated once, so its use costs nothing. *)
Definition big : nat := expensive 100.

Definition use_big (n : nat) : nat := big + n.

TimeFun use_big.

Example closed_constant_free : T_use_big 0 = 1 + Nat.T_add big 0 := eq_refl.

Definition opaque_double (n : nat) : nat.
Proof.
  exact (n + n).
Qed.

TimePrim opaque_double := (fun n => n + 1).

Definition use_opaque (n : nat) : nat := opaque_double n.

TimeFun use_opaque.

Example prim_cost : T_use_opaque 4 = 6 := eq_refl.

(** * Universe polymorphism and implicit arguments *)

Polymorphic Definition poly_id@{u} {A : Type@{u}} (x : A) : A := x.

TimeFun poly_id.

(** The universe instance is accepted only by a universe-polymorphic constant. *)
Example poly_id_polymorphic : @T_poly_id@{Set} nat 0 = 1 := eq_refl.

(** [T_length] copies the implicit argument of [length]. *)
Example length_implicit : Datatypes.T_length [1; 2] = 3 := eq_refl.

(** The companion follows the function argument explicitly. *)
Example fold_left_companion : List.T_fold_left Nat.add Nat.T_add [1; 2] 0 = 6 := eq_refl.

(** * Sections *)

Section Lengths.

Variable A : Type.

Fixpoint len (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: r => S (len r)
  end.

End Lengths.

TimeFun len.

Example len_after_section : T_len nat [1; 2] = 3 := eq_refl.

(** * Convoys and primitive projections *)

(** A match applied to a proof, the convoy pattern, keeps its proof binder in the time
    function. *)
Definition head_plus_one (l : list nat) : nat :=
  (match l return l = l -> nat with
   | [] => fun _ => 0
   | x :: _ => fun _ => x + 1
   end) eq_refl.

TimeFun head_plus_one.

Example convoy_cost : T_head_plus_one [4] = 1 + Nat.T_add 4 1 := eq_refl.

#[projections(primitive)]
Record point : Type := {
  px : nat;
  py : nat
}.

Definition point_sum (p : point) : nat := px p + py p.

TimeFun point_sum.

Example projection_cost : T_point_sum {| px := 2; py := 3 |} = 1 + Nat.T_add 2 3 := eq_refl.

(** * Checking *)

TimeCheck expensive redex partial sum let_fun sum_to even odd monadic size size_local poly_id
  head_plus_one point_sum.

TimeAudit use_opaque size partial.

(** [TimeCheck] notices a time function that no longer matches its translation: here [wrap]
    becomes unfolded after [use_wrap] was derived. *)
Definition wrap (n : nat) : nat := S n.

Definition use_wrap (n : nat) : nat := wrap n.

TimeFun wrap use_wrap.

TimeUnfold wrap.

Fail TimeCheck use_wrap.

Fail TimeAudit use_wrap.

(** * The table of built-in costs

    [TimePrimTable] prints the costs declared with [TimePrim] and fails unless the constants with
    a declared cost are exactly the given ones, here the two of this file. *)
Definition opaque_triple (n : nat) : nat.
Proof.
  exact (n + n + n).
Qed.

TimePrim opaque_triple := 3.

TimePrimTable opaque_double opaque_triple.

Fail TimePrimTable opaque_double.
