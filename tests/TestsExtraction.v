(** * Extraction of the accessibility loop

    This file extracts [loop] and [countdown].  The extracted [loop] takes the step function
    and the state only: the relation and the accessibility proof are erased, and there is no
    fuel.  No time function is reachable from the extracted code.  The build log records the
    output, and the report quotes it.  The file also audits the roots of the examples.

    For example, the extracted [countdown] calls [loop] with [count_step] and its argument.

    Builds on: Time Loop Trie Queue KeyedMap Loops *)

From Stdlib Require Extraction.
From Argent Require Import Time Loop.
From Argent.Examples Require Trie Queue KeyedMap Loops.

Extraction loop.

Recursive Extraction Loops.countdown.

(** Every computational constant reachable from the example roots has a checked time function
    or a declared cost. *)
TimeAudit Trie.get Trie.set Trie.remove Queue.step Loops.countdown Loops.count
  KeyedMap.NatSum.sum_values.