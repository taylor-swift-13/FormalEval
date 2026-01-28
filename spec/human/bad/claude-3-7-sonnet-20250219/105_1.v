Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.InsertionSort.
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
    (Permutation l_filtered l_sorted /\ Sorted Z.le l_sorted) /\
    let l_reversed := rev l_sorted in
    l_out = map digit_to_word l_reversed.

(* Auxiliary lemmas about insertion sort *)

Lemma insertion_sort_sorted : forall l, Sorted Z.le (insertion_sort Z.le l).
Proof.
  apply insertion_sort_sorted.
Qed.

Lemma insertion_sort_perm : forall l,
  Permutation l (insertion_sort Z.le l).
Proof.
  apply insertion_sort_perm.
Qed.

Example problem_105_example :
  problem_105_spec [2; 1; 1; 4; 5; 8; 2; 3]
                   ["Eight"; "Five"; "Four"; "Three"; "Two"; "Two"; "One"; "One"].
Proof.
  unfold problem_105_spec.
  set (l := [2;1;1;4;5;8;2;3]).
  set (l_filtered := filter is_target_digit l).
  assert (Hfilter: l_filtered = l).
  { (* all elements are between 1 and 9 *)
    unfold l, l_filtered.
    simpl.
    repeat (rewrite andb_true_iff).
    reflexivity.
  }
  rewrite Hfilter.
  exists (insertion_sort Z.le l_filtered).
  split.
  - split.
    + apply insertion_sort_perm.
    + apply insertion_sort_sorted.
  - simpl.
    rewrite rev_map.
    (* l_filtered = [2;1;1;4;5;8;2;3] *)
    (* insertion_sort Z.le l_filtered = sorted list *)
    (* We must identify the sorted list *)
    assert (Hsortedlist:
      insertion_sort Z.le l_filtered = [1;1;2;2;3;4;5;8]).
    {
      (* Insertion sort on the list must produce this sorted list *)
      apply Permutation_insertion_sort in l_filtered.
      apply Permutation_sorted_unique with (l2 := [1;1;2;2;3;4;5;8]); auto.
      - apply insertion_sort_sorted.
      - repeat constructor; lia.
      - split.
        + repeat constructor; lia.
        + repeat constructor; lia.
    }
    rewrite Hsortedlist.
    reflexivity.
Qed.