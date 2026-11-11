(** * Assumptions of the example theorems

    This file prints the assumptions of every theorem of the examples and of the library's
    potential lemmas.  Each one must print "Closed under the global context".  The build log
    records the output, and the report quotes it.

    For example, [Print Assumptions Trie.get_tight] shows that the tightness of [get] uses no
    axiom.

    Builds on: Trie Queue KeyedMap Loops Amortised Loop BigO *)

From Argent Require Import Amortised Loop BigO.
From Argent.Examples Require Trie Queue KeyedMap Loops.

Print Assumptions Trie.T_get_le.
Print Assumptions Trie.T_set_le.
Print Assumptions Trie.T_remove_le.
Print Assumptions Trie.T_get_ge.
Print Assumptions Trie.get_bigO.
Print Assumptions Trie.set_bigO.
Print Assumptions Trie.remove_bigO.
Print Assumptions Trie.get_tight.
Print Assumptions Queue.step_amortised.
Print Assumptions Queue.queue_total.
Print Assumptions KeyedMap.NatMap.T_get_le.
Print Assumptions KeyedMap.NatMap.T_set_le.
Print Assumptions KeyedMap.NatKey.T_encode_le.
Print Assumptions KeyedMap.NatSum.T_sum_values_le.
Print Assumptions Loops.T_countdown_le.
Print Assumptions Loops.T_count_le.
Print Assumptions Loops.countdown_runs.
Print Assumptions amortised_run.
Print Assumptions amortised_uniform.
Print Assumptions T_loop_le.
Print Assumptions T_loop_fuel_le.
Print Assumptions bigO_trans.
