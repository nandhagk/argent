(** * Time functions on large inputs

    This file evaluates derived time functions on large lists with [vm_compute] and compares
    each result with a literal of type [N].  A time value is a binary number, so the time of
    1,000,001 steps is a literal of 20 bits.  A time value of type [nat] would be a term of
    1,000,001 constructors.

    [List.T_rev] evaluates [rev] of every suffix of its argument, because the time of the
    append at each step takes the reversed suffix as its argument.  So its evaluation takes
    time cubic in the length of the list, and the test uses 1,000 elements, which take a few
    seconds.  The linear [List.T_rev_append] runs on 1,000,000 elements.

    For example, [List.T_rev] on [n] elements is [n * (n + 1) / 2 + n + 1], which is 501,501
    for 1,000 elements.

    Builds on: Time Std *)

From Stdlib Require Import List NArith.
From Argent Require Import Time Std.
Import List.ListNotations.

(** The time of reversing a list of 1,000 elements with [rev]. *)
Example rev_large : List.T_rev (repeat tt 1000) = 501501%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** The time of reversing a list of 1,000,000 elements with [rev_append].  The length is a
    literal of type [N], converted to [nat] by [N.to_nat], because Rocq warns about a [nat]
    literal above 5,000. *)
Example rev_append_large : List.T_rev_append (repeat tt (N.to_nat 1000000)) [] = 1000001%N.
Proof.
  vm_compute. reflexivity.
Qed.
