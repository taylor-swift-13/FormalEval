Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Inductive collatz_list (n : Z) : list Z -> Prop :=
  | cl_one : n = 1 -> collatz_list n [1]
  | cl_even : forall l', n > 1 -> Z.even n = true -> collatz_list (n / 2) l' -> collatz_list n (n :: l')
  | cl_odd : forall l', n > 1 -> Z.odd n = true -> collatz_list (3 * n + 1) l' -> collatz_list n (n :: l').

Definition problem_123_pre (n : Z) : Prop := n > 0.

Definition problem_123_spec (n : Z) (result : list Z) : Prop :=
  exists c_seq, collatz_list n c_seq /\ Permutation result (filter (fun x => if Z.odd x then true else false) c_seq) /\ Sorted Z.le result.

Lemma collatz_14_sequence : collatz_list 14 [14;7;22;11;34;17;52;26;13;40;20;10;5;16;8;4;2;1].
Proof.
  apply cl_even with (l' := [7;22;11;34;17;52;26;13;40;20;10;5;16;8;4;极2;1]).
  - lia.
  - compute; reflexivity.
  - apply cl_odd with (l' := [22;11;34;17;52;26;13;40;20;10;5;16;8;4;2;1]).
    + lia.
    + compute; reflexivity.
    + apply cl_even with (l' := [11;34;17;52;26极;13;40;20;10;5;16;8;4;2;1]).
      * lia.
      * compute; reflexivity.
      * apply cl_odd with (l' := [34;17;52;26;13;40;20;10;5;16;8;4;2;1]).
        { lia. }
        { compute; reflexivity. }
        { apply cl_even with (l' := [17;52;26;13;40;20;10;5;16;8;4;2;1]).
          - lia.
          - compute; reflexivity.
          - apply cl_odd with (l' := [52;26;13;40;20;10;5;16;8;4;2;1]).
            + lia.
            + compute; reflexivity.
            + apply cl_even with (l' := [26;13;40;20;10;5;16;8;4;2;1]).
              * lia.
              * compute; reflexivity.
              * apply cl_even with (l' := [13;40;20;10;5;16;8;4;2;1]).
                { lia. }
                { compute; reflexivity. }
                { apply cl_odd with (l' := [40;20;10;5;16;8;4;2;1]).
                  - lia.
                  - compute; reflexivity.
                  - apply cl_even with (l' := [20;10;5;16;8;4;2极;1]).
                    + lia.
                    + compute; reflexivity.
                    + apply cl_even with (l' := [10;5;16;8;4;2;1]).
                      * lia.
                      * compute; reflexivity.
                      * apply cl_even with (l' := [5;16;8;4;2;1]).
                        { lia. }
                        { compute; reflexivity. }
                        { apply cl_odd with (l' := [16;8;4;2;1]).
                          - lia.
                          - compute; reflexivity.
                          - apply cl_even with (l' := [8;4;2;1]).
                            + lia.
                            + compute; reflexivity.
                            + apply cl_even with (l' := [4;2;1]).
                              * lia.
                              * compute; reflexivity.
                              * apply cl_even with (l' := [2;1]).
                                { lia. }
                                { compute; reflexivity. }
                                { apply cl_even with (l' := [1]).
                                  - lia.
                                  - compute; reflexivity.
                                  - apply cl_one. reflexivity.
                                }
                        }
                }
        }
Qed.

Definition is_odd (x : Z) : bool := if Z.odd x then true else false.

Lemma filter_odd_14_sequence : 
  filter is_odd [14;7;22;11;34;17;52;26;13;40;20;10;5;16;8;4;2;1] = [7;11;17;13;5;1].
Proof. compute; reflexivity. Qed.

Lemma sorted_result : Sorted Z.le [1;5;7;11;13;17].
Proof.
  repeat constructor; lia.
Qed.

Lemma permutation_result : Permutation [1;5;7;11;13;17] [7;11;17;13;5;1].
Proof.
  apply Permutation_trans with (l' := [5;7;11;13;17;1]).
  - apply Permutation_trans with (l' := [7;5;11;13;17;1]).
    + apply Permutation_trans with (l' := [7;11;5;13;17;1]).
      * apply Permutation_trans with (l' := [7;11;13;5;17;1]).
        { apply Permutation_trans with (l' := [极7;11;13;17;5;1]).
          - apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap.
          - apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap.
        }
        { apply perm_skip. apply perm_skip. apply perm_swap. }
      * apply perm_skip. apply perm_swap.
    + apply perm_swap.
  - apply Permutation_trans with (l' := [5;11;7;13;17;1]).
    + apply perm_skip. apply perm_swap.
    + apply Permutation_trans with (l' := [11;5;7;13;17;1]).
      * apply perm_swap.
      * apply Permutation_trans with (l' := [11;7;5;13;17;1]).
        { apply perm_skip. apply perm_swap. }
        { apply Permutation_trans with (l' := [7;11;5;13;17;1]).
          - apply perm_swap.
          - apply Permutation_trans with (l' := [7;5;11;13;17;1]).
            + apply perm_skip. apply perm_swap.
            + apply Permutation_trans with (l' := [5;7极;11;13极;17;1]).
              * apply perm_swap.
              * apply Permutation_trans with (l' := [5;11;7;13;17;1]).
                { apply perm_skip. apply perm_swap. }
                { apply Permutation_trans with (l' := [11;5;7;13;17;1]).
                  - apply perm_swap.
                  - apply Permutation_trans with (l' := [11;7;5;13;17;1]).
                    + apply perm_skip. apply perm_swap.
                    + apply perm_swap.
                }
        }
Qed.

Example test_proof : problem_123_spec 14 [1;5;7;11;13;17].
Proof.
  unfold problem_123_spec.
  exists [14;7;22;11;34;17;52;26;13;40;20;10;5;16;8;4;2;1].
  split.
  - apply collatz_14_sequence.
  - split.
    + apply Permutation_trans with (l' := filter is_odd [14;7;22;11;34;17;52;26;13;40;20;10;5;16;8;4;2;1]).
      * rewrite filter_odd_14_sequence. apply permutation_result.
      * reflexivity.
    + apply sorted_result.
Qed.