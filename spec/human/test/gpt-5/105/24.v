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
    [4%Z; 3%Z; 2%Z; 1%Z; 9%Z; 8%Z; 7%Z; 6%Z; 2%Z]
    ["Nine"%string; "Eight"%string; "Seven"%string; "Six"%string; "Four"%string; "Three"%string; "Two"%string; "Two"%string; "One"%string].
Proof.
  unfold problem_105_spec.
  set (l_filtered := filter is_target_digit [4%Z; 3%Z; 2%Z; 1%Z; 9%Z; 8%Z; 7%Z; 6%Z; 2%Z]).
  exists [1%Z; 2%Z; 2%Z; 3%Z; 4%Z; 6%Z; 7%Z; 8%Z; 9%Z].
  split.
  - split.
    + assert (Hfilt : l_filtered = [4%Z; 3%Z; 2%Z; 1%Z; 9%Z; 8%Z; 7%Z; 6%Z; 2%Z]).
      { unfold l_filtered. vm_compute. reflexivity. }
      rewrite Hfilt.
      assert (H0 : Permutation
                     [4%Z;3%Z;2%Z;1%Z;9%Z;8%Z;7%Z;6%Z;2%Z]
                     [3%Z;4%Z;2%Z;1%Z;9%Z;8%Z;7%Z;6%Z;2%Z]).
      { apply perm_swap. }
      assert (H1 : Permutation
                     [3%Z;4%Z;2%Z;1%Z;9%Z;8%Z;7%Z;6%Z;2%Z]
                     [3%Z;2%Z;4%Z;1%Z;9%Z;8%Z;7%Z;6%Z;2%Z]).
      { apply perm_skip. apply perm_swap. }
      assert (H2 : Permutation
                     [3%Z;2%Z;4%Z;1%Z;9%Z;8%Z;7%Z;6%Z;2%Z]
                     [2%Z;3%Z;4%Z;1%Z;9%Z;8%Z;7%Z;6%Z;2%Z]).
      { apply perm_swap. }
      assert (H3 : Permutation
                     [2%Z;3%Z;4%Z;1%Z;9%Z;8%Z;7%Z;6%Z;2%Z]
                     [2%Z;3%Z;1%Z;4%Z;9%Z;8%Z;7%Z;6%Z;2%Z]).
      { apply perm_skip. apply perm_skip. apply perm_swap. }
      assert (H4 : Permutation
                     [2%Z;3%Z;1%Z;4%Z;9%Z;8%Z;7%Z;6%Z;2%Z]
                     [2%Z;1%Z;3%Z;4%Z;9%Z;8%Z;7%Z;6%Z;2%Z]).
      { apply perm_skip. apply perm_swap. }
      assert (H5 : Permutation
                     [2%Z;1%Z;3%Z;4%Z;9%Z;8%Z;7%Z;6%Z;2%Z]
                     [1%Z;2%Z;3%Z;4%Z;9%Z;8%Z;7%Z;6%Z;2%Z]).
      { apply perm_swap. }
      assert (H6 : Permutation
                     [1%Z;2%Z;3%Z;4%Z;9%Z;8%Z;7%Z;6%Z;2%Z]
                     [1%Z;2%Z;3%Z;4%Z;9%Z;8%Z;7%Z;2%Z;6%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H7 : Permutation
                     [1%Z;2%Z;3%Z;4%Z;9%Z;8%Z;7%Z;2%Z;6%Z]
                     [1%Z;2%Z;3%Z;4%Z;9%Z;8%Z;2%Z;7%Z;6%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H8 : Permutation
                     [1%Z;2%Z;3%Z;4%Z;9%Z;8%Z;2%Z;7%Z;6%Z]
                     [1%Z;2%Z;3%Z;4%Z;9%Z;2%Z;8%Z;7%Z;6%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H9 : Permutation
                     [1%Z;2%Z;3%Z;4%Z;9%Z;2%Z;8%Z;7%Z;6%Z]
                     [1%Z;2%Z;3%Z;4%Z;2%Z;9%Z;8%Z;7%Z;6%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H10 : Permutation
                      [1%Z;2%Z;3%Z;4%Z;2%Z;9%Z;8%Z;7%Z;6%Z]
                      [1%Z;2%Z;3%Z;2%Z;4%Z;9%Z;8%Z;7%Z;6%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H11 : Permutation
                      [1%Z;2%Z;3%Z;2%Z;4%Z;9%Z;8%Z;7%Z;6%Z]
                      [1%Z;2%Z;2%Z;3%Z;4%Z;9%Z;8%Z;7%Z;6%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H12 : Permutation
                      [1%Z;2%Z;2%Z;3%Z;4%Z;9%Z;8%Z;7%Z;6%Z]
                      [1%Z;2%Z;2%Z;3%Z;4%Z;8%Z;9%Z;7%Z;6%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H13 : Permutation
                      [1%Z;2%Z;2%Z;3%Z;4%Z;8%Z;9%Z;7%Z;6%Z]
                      [1%Z;2%Z;2%Z;3%Z;4%Z;8%Z;7%Z;9%Z;6%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H14 : Permutation
                      [1%Z;2%Z;2%Z;3%Z;4%Z;8%Z;7%Z;9%Z;6%Z]
                      [1%Z;2%Z;2%Z;3%Z;4%Z;8%Z;7%Z;6%Z;9%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H15 : Permutation
                      [1%Z;2%Z;2%Z;3%Z;4%Z;8%Z;7%Z;6%Z;9%Z]
                      [1%Z;2%Z;2%Z;3%Z;4%Z;8%Z;6%Z;7%Z;9%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H16 : Permutation
                      [1%Z;2%Z;2%Z;3%Z;4%Z;8%Z;6%Z;7%Z;9%Z]
                      [1%Z;2%Z;2%Z;3%Z;4%Z;6%Z;8%Z;7%Z;9%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      assert (H17 : Permutation
                      [1%Z;2%Z;2%Z;3%Z;4%Z;6%Z;8%Z;7%Z;9%Z]
                      [1%Z;2%Z;2%Z;3%Z;4%Z;6%Z;7%Z;8%Z;9%Z]).
      { repeat (apply perm_skip). apply perm_swap. }
      eapply perm_trans. exact H0.
      eapply perm_trans. exact H1.
      eapply perm_trans. exact H2.
      eapply perm_trans. exact H3.
      eapply perm_trans. exact H4.
      eapply perm_trans. exact H5.
      eapply perm_trans. exact H6.
      eapply perm_trans. exact H7.
      eapply perm_trans. exact H8.
      eapply perm_trans. exact H9.
      eapply perm_trans. exact H10.
      eapply perm_trans. exact H11.
      eapply perm_trans. exact H12.
      eapply perm_trans. exact H13.
      eapply perm_trans. exact H14.
      eapply perm_trans. exact H15.
      eapply perm_trans. exact H16.
      eapply perm_trans. exact H17.
      apply Permutation_refl.
    + repeat constructor; try lia.
  - simpl. reflexivity.
Qed.