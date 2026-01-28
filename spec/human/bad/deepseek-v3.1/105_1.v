Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Compare_dec.
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

Definition problem_105_spec (l_in : list Z) (l_out : list string) : Prop :=
  let l_filtered := filter is_target_digit l_in in
  exists (l_sorted : list Z),
    (Permutation l_filtered l_sorted /\
     Sorted Z.le l_sorted) /\
    let l_reversed := rev l_sorted in
    l_out = map digit_to_word l_reversed.

Example test_case_1 :
  problem_105_spec [2; 1; 1; 4; 5; 8; 2; 3]
                  ["Eight"; "Five"; "Four"; "Three"; "Two"; "Two"; "One"; "One"].
Proof.
  unfold problem_105_spec.
  exists [1; 1; 2; 2; 3; 4; 5; 8].
  split.
  - split.
    + unfold is_target_digit.
      compute.
      repeat constructor.
    + repeat constructor; try lia.
      * constructor.
      * constructor.
      * constructor; lia.
      * constructor; lia.
      * constructor; lia.
      * constructor; lia.
      * constructor; lia.
      * constructor.
  - simpl.
    reflexivity.
Qed.