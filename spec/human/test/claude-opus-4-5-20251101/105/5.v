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

Example test_problem_105 :
  problem_105_spec [9%Z; 4%Z; 8%Z]
                   ["Nine"; "Eight"; "Four"]%string.
Proof.
  unfold problem_105_spec.
  simpl filter.
  exists [4; 8; 9]%Z.
  split.
  - split.
    + apply perm_trans with (l' := [4; 9; 8]).
      { apply perm_swap. }
      apply perm_trans with (l' := [4; 8; 9]).
      { apply perm_skip. apply perm_swap. }
      apply Permutation_refl.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_nil.
        -- apply HdRel_cons. lia.
      * apply HdRel_cons. lia.
  - simpl. reflexivity.
Qed.