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
  problem_105_spec [2%Z; 1%Z; 1%Z; 4%Z; 5%Z; 8%Z; 2%Z; 3%Z]
                   ["Eight"; "Five"; "Four"; "Three"; "Two"; "Two"; "One"; "One"]%string.
Proof.
  unfold problem_105_spec.
  simpl filter.
  (* l_filtered = [2; 1; 1; 4; 5; 8; 2; 3] *)
  exists [1; 1; 2; 2; 3; 4; 5; 8]%Z.
  split.
  - split.
    + (* Permutation [2; 1; 1; 4; 5; 8; 2; 3] [1; 1; 2; 2; 3; 4; 5; 8] *)
      apply perm_trans with (l' := [1; 2; 1; 4; 5; 8; 2; 3]).
      { apply perm_swap. }
      apply perm_trans with (l' := [1; 1; 2; 4; 5; 8; 2; 3]).
      { apply perm_skip. apply perm_swap. }
      apply perm_trans with (l' := [1; 1; 2; 4; 5; 2; 8; 3]).
      { apply perm_skip. apply perm_skip. apply perm_skip. 
        apply perm_skip. apply perm_skip. apply perm_swap. }
      apply perm_trans with (l' := [1; 1; 2; 4; 2; 5; 8; 3]).
      { apply perm_skip. apply perm_skip. apply perm_skip. 
        apply perm_skip. apply perm_swap. }
      apply perm_trans with (l' := [1; 1; 2; 2; 4; 5; 8; 3]).
      { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
      apply perm_trans with (l' := [1; 1; 2; 2; 4; 5; 3; 8]).
      { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip.
        apply perm_skip. apply perm_skip. apply perm_swap. }
      apply perm_trans with (l' := [1; 1; 2; 2; 4; 3; 5; 8]).
      { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip.
        apply perm_skip. apply perm_swap. }
      apply perm_trans with (l' := [1; 1; 2; 2; 3; 4; 5; 8]).
      { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip.
        apply perm_swap. }
      apply Permutation_refl.
    + (* Sorted Z.le [1; 1; 2; 2; 3; 4; 5; 8] *)
      apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_cons.
                 --- apply Sorted_cons.
                     +++ apply Sorted_cons.
                         *** apply Sorted_cons.
                             ---- apply Sorted_nil.
                             ---- apply HdRel_nil.
                         *** apply HdRel_cons. lia.
                     +++ apply HdRel_cons. lia.
                 --- apply HdRel_cons. lia.
              ** apply HdRel_cons. lia.
           ++ apply HdRel_cons. lia.
        -- apply HdRel_cons. lia.
      * apply HdRel_cons. lia.
  - (* map digit_to_word (rev [1; 1; 2; 2; 3; 4; 5; 8]) = ... *)
    simpl. reflexivity.
Qed.