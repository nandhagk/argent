(** * Assumptions of the example theorems

    - [Print Assumptions] on every theorem of the examples, on the potential lemmas of the
      library and on the lemmas of [Complexity].
    - Each one must print "Closed under the global context".

    For example, [Print Assumptions Trie.get_worst_complexity] shows that the worst-case
    tightness of [get] uses no axiom.

    Builds on: Lists Trie Queue KeyedMap Loops Halving Amortised Loop Complexity Std *)

From Argent Require Import Amortised Loop Complexity Std.
From Argent.Examples Require Lists Trie Queue KeyedMap Loops Halving.

Print Assumptions Lists.T_append_exact.
Print Assumptions Lists.T_append_le.
Print Assumptions Lists.append_complexity.
Print Assumptions Lists.T_slow_rev_le.
Print Assumptions Lists.T_rev_onto_exact.
Print Assumptions Lists.T_map_le.
Print Assumptions Lists.T_add_to_all_le.
Print Assumptions Trie.T_get_le.
Print Assumptions Trie.T_set_le.
Print Assumptions Trie.T_remove_le.
Print Assumptions Trie.T_get_ge.
Print Assumptions Trie.get_complexity.
Print Assumptions Trie.set_complexity.
Print Assumptions Trie.remove_complexity.
Print Assumptions Trie.get_worst_complexity.
Print Assumptions Queue.step_amortised.
Print Assumptions Queue.queue_total.
Print Assumptions KeyedMap.NatMap.T_get_le.
Print Assumptions KeyedMap.NatMap.T_set_le.
Print Assumptions KeyedMap.NatKey.T_encode_le.
Print Assumptions KeyedMap.NatSum.T_sum_values_le.
Print Assumptions Loops.T_countdown_le.
Print Assumptions Loops.T_count_le.
Print Assumptions Loops.countdown_runs.
Print Assumptions Halving.T_log2_le.
Print Assumptions Halving.T_halves_le.
Print Assumptions Halving.log2_runs.
Print Assumptions Wf.T_Fix_F_le.
Print Assumptions Wf.T_Fix_le.
Print Assumptions Wf.T_well_founded_induction_type_le.
Print Assumptions Z.T_div_eucl_le.
Print Assumptions Z.T_gcd_le.
Print Assumptions amortised_run.
Print Assumptions amortised_uniform.
Print Assumptions T_loop_le.
Print Assumptions T_loop_fuel_le.
Print Assumptions bigO_trans.
Print Assumptions bigO_subset.
Print Assumptions bigOmega_intro.
Print Assumptions bigOmega_le.
Print Assumptions bigOmega_mono.
Print Assumptions bigOmega_add.
Print Assumptions bigOmega_trans.
Print Assumptions bigOmega_comp.
Print Assumptions bigTheta_intro.
Print Assumptions bigTheta_shift.
Print Assumptions bigTheta_sym.
Print Assumptions bigTheta_add.
Print Assumptions bigTheta_trans.
Print Assumptions bigTheta_comp.
Print Assumptions tight_iff.
Print Assumptions bigOmega_worst_intro.
Print Assumptions bigOmega_worst_of_bigOmega.
Print Assumptions tight_of_bigTheta.
Print Assumptions bigO_amortised_intro.
Print Assumptions bigO_amortised_sub.
Print Assumptions bigO_amortised_of_bigO.
Print Assumptions bigO_amortised_run.
