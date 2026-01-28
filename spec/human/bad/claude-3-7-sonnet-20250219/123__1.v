Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Inductive collatz_list (n : Z) : list Z -> Prop :=
  | cl_one : n = 1 -> collatz_list n [1]
  | cl_even : forall l',
      n > 1 ->
      Z.even n = true ->
      collatz_list (n / 2) l' ->
      collatz_list n (n :: l')
  | cl_odd : forall l',
      n > 1 ->
      Z.odd n = true ->
      collatz_list (3 * n + 1) l' ->
      collatz_list n (n :: l').

Definition problem_123_pre (n : Z) : Prop := n > 0.

Definition  problem_123_spec (n : Z) (result : list Z) : Prop :=
  exists (c_seq : list Z),
    collatz_list n c_seq /\
    Permutation result (filter (fun x => Z.odd x) c_seq) /\
    Sorted Z.le result.

Example collatz_14_sequence :
  collatz_list 14
  [14; 7; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' :=
    [7; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply cl_odd with (l' :=
      [22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
    + lia.
    + reflexivity.
    + apply cl_even with (l' :=
        [11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
      * lia.
      * reflexivity.
      * apply cl_odd with (l' :=
          [34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
        -- lia.
        -- reflexivity.
        -- apply cl_even with (l' :=
            [17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
          ++ lia.
          ++ reflexivity.
          ++ apply cl_odd with (l' :=
              [52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
             ** lia.
             ** reflexivity.
             ** apply cl_even with (l' :=
                 [26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
                --- lia.
                --- reflexivity.
                --- apply cl_even with (l' :=
                    [13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
                   +++ lia.
                   +++ reflexivity.
                   +++ apply cl_odd with (l' :=
                       [40; 20; 10; 5; 16; 8; 4; 2; 1]).
                       * lia.
                       * reflexivity.
                       * apply cl_even with (l' :=
                           [20; 10; 5; 16; 8; 4; 2; 1]).
                          ++ lia.
                          ++ reflexivity.
                          ++ apply cl_even with (l' :=
                              [10; 5; 16; 8; 4; 2; 1]).
                             ** lia.
                             ** reflexivity.
                             ** apply cl_even with (l' :=
                                 [5; 16; 8; 4; 2; 1]).
                                --- lia.
                                --- reflexivity.
                                --- apply cl_odd with (l' :=
                                    [16; 8; 4; 2; 1]).
                                    +++ lia.
                                    +++ reflexivity.
                                    +++ apply cl_even with (l' :=
                                        [8; 4; 2; 1]).
                                        *** lia.
                                        *** reflexivity.
                                        *** apply cl_even with (l' :=
                                            [4; 2; 1]).
                                            ++++ lia.
                                            ++++ reflexivity.
                                            ++++ apply cl_even with (l' :=
                                                [2; 1]).
                                                **** lia.
                                                **** reflexivity.
                                                **** apply cl_even with (l' := [1]).
                                                      lia.
                                                      reflexivity.
                                                      apply cl_one.
                                                      reflexivity.
Qed.

Example test_get_odd_collatz_14 :
  problem_123_spec 14 [1; 5; 7; 11; 13; 17].
Proof.
  unfold problem_123_spec.
  exists [14;7;22;11;34;17;52;26;13;40;20;10;5;16;8;4;2;1].
  split.
  - apply collatz_14_sequence.
  - split.
    + assert (Hfilter :
        filter (fun x => Z.odd x)
          [14;7;22;11;34;17;52;26;13;40;20;10;5;16;8;4;2;1] 
        = [7;11;17;13;5;1]).
      {
        repeat (cbn;
                match goal with
                | |- context [Z.odd ?n] => destruct (Z.odd n) eqn:?; reflexivity || idtac
                end).
      }
      rewrite Hfilter.
      apply Permutation_sym.
      (* Prove Permutation [7;11;17;13;5;1] [1;5;7;11;13;17] by swaps *)
      repeat (apply perm_swap || apply perm_trans).
      apply Permutation_refl.
    + repeat constructor; lia.
Qed.