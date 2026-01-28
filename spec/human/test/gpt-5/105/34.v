Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Permutation.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_target_digit (z : Z) : bool :=
  (1 <=? z) && (z <=? 9).

Definition digit_to_word (z : Z) : string :=
  match z with
  | 1 => "One"%string
  | 2 => "Two"%string
  | 3 => "Three"%string
  | 4 => "Four"%string
  | 5 => "Five"%string
  | 6 => "Six"%string
  | 7 => "Seven"%string
  | 8 => "Eight"%string
  | 9 => "Nine"%string
  | _ => ""%string
  end.

Definition problem_105_pre (l_in : list Z) : Prop := True.

Definition problem_105_spec (l_in : list Z) (l_out : list string) : Prop :=
  let l_filtered := filter is_target_digit l_in in
  exists (l_sorted : list Z),
    (Permutation l_filtered l_sorted /\
     Sorted Z.le l_sorted) /\
    let l_reversed := rev l_sorted in
    l_out = map digit_to_word l_reversed.

Example problem_105_test_1 :
  problem_105_spec
    [4%Z; 2%Z; 1%Z; 9%Z; 8%Z; 7%Z; 6%Z; 2%Z]
    ["Nine"%string; "Eight"%string; "Seven"%string; "Six"%string; "Four"%string; "Two"%string; "Two"%string; "One"%string].
Proof.
  unfold problem_105_spec.
  set (l_filtered := filter is_target_digit [4%Z; 2%Z; 1%Z; 9%Z; 8%Z; 7%Z; 6%Z; 2%Z]).
  exists [1%Z; 2%Z; 2%Z; 4%Z; 6%Z; 7%Z; 8%Z; 9%Z].
  split.
  - split.
    + assert (Hfilt : l_filtered = [4%Z; 2%Z; 1%Z; 9%Z; 8%Z; 7%Z; 6%Z; 2%Z]).
      { unfold l_filtered. vm_compute. reflexivity. }
      rewrite Hfilt.
      eapply perm_trans.
      * apply perm_swap.
      * eapply perm_trans.
        -- apply perm_skip. apply perm_swap.
        -- eapply perm_trans.
           ++ apply perm_swap.
           ++ eapply perm_trans.
              ** assert (Htail4 : Permutation [4%Z;9%Z;8%Z;7%Z;6%Z;2%Z] [4%Z;9%Z;8%Z;7%Z;2%Z;6%Z]).
                 { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
                 assert (Htail3 : Permutation [4%Z;9%Z;8%Z;7%Z;2%Z;6%Z] [4%Z;9%Z;8%Z;2%Z;7%Z;6%Z]).
                 { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
                 assert (Htail2 : Permutation [4%Z;9%Z;8%Z;2%Z;7%Z;6%Z] [4%Z;9%Z;2%Z;8%Z;7%Z;6%Z]).
                 { apply perm_skip. apply perm_skip. apply perm_swap. }
                 assert (Htail1 : Permutation [4%Z;9%Z;2%Z;8%Z;7%Z;6%Z] [4%Z;2%Z;9%Z;8%Z;7%Z;6%Z]).
                 { apply perm_skip. apply perm_swap. }
                 eapply perm_trans.
                 *** apply perm_skip. apply perm_skip. exact Htail4.
                 *** eapply perm_trans.
                     ---- apply perm_skip. apply perm_skip. exact Htail3.
                     ---- eapply perm_trans.
                          ++++ apply perm_skip. apply perm_skip. exact Htail2.
                          ++++ eapply perm_trans.
                               ***** apply perm_skip. apply perm_skip. exact Htail1.
                               ***** apply perm_skip. apply perm_skip. apply perm_swap.
              ** assert (Ha1 : Permutation [4%Z;9%Z;8%Z;7%Z;6%Z] [4%Z;9%Z;8%Z;6%Z;7%Z]).
                 { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
                 assert (Ha2 : Permutation [4%Z;9%Z;8%Z;6%Z;7%Z] [4%Z;9%Z;6%Z;8%Z;7%Z]).
                 { apply perm_skip. apply perm_skip. apply perm_swap. }
                 assert (Ha3 : Permutation [4%Z;9%Z;6%Z;8%Z;7%Z] [4%Z;6%Z;9%Z;8%Z;7%Z]).
                 { apply perm_skip. apply perm_swap. }
                 assert (Hb1 : Permutation [4%Z;6%Z;9%Z;8%Z;7%Z] [4%Z;6%Z;9%Z;7%Z;8%Z]).
                 { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
                 assert (Hb2 : Permutation [4%Z;6%Z;9%Z;7%Z;8%Z] [4%Z;6%Z;7%Z;9%Z;8%Z]).
                 { apply perm_skip. apply perm_skip. apply perm_swap. }
                 assert (Hb3 : Permutation [4%Z;6%Z;7%Z;9%Z;8%Z] [4%Z;6%Z;7%Z;8%Z;9%Z]).
                 { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
                 eapply perm_trans.
                 *** apply perm_skip. apply perm_skip. apply perm_skip. exact Ha1.
                 *** eapply perm_trans.
                     ---- apply perm_skip. apply perm_skip. apply perm_skip. exact Ha2.
                     ---- eapply perm_trans.
                          ++++ apply perm_skip. apply perm_skip. apply perm_skip. exact Ha3.
                          ++++ eapply perm_trans.
                               ***** apply perm_skip. apply perm_skip. apply perm_skip. exact Hb1.
                               ***** eapply perm_trans.
                                    ------ apply perm_skip. apply perm_skip. apply perm_skip. exact Hb2.
                                    ------ apply perm_skip. apply perm_skip. apply perm_skip. exact Hb3.
    + repeat constructor; try lia.
  - simpl. reflexivity.
Qed.