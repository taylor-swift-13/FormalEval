Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [1; 2; 3; 5; 16; -11; 16; -8; 9; -12; 7; -12; 16] 
  [-12; 2; 3; 1; 16; -11; 5; -8; 9; 16; 7; -12; 16].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 13 (destruct i; [
        simpl in *;
        try (exfalso; apply H; reflexivity);
        try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-12; 1; 5; 16; 16] [1; 5; 16; -12; 16] *)
        (* We show that moving -12 to the correct position in the second list makes them equal *)
        change [-12; 1; 5; 16; 16] with (-12 :: ([1; 5; 16] ++ [16])).
        change [1; 5; 16; -12; 16] with ([1; 5; 16] ++ -12 :: [16]).
        apply Permutation_middle.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [
          simpl; try (apply HdRel_cons; lia); try apply HdRel_nil 
        | ]).
        apply Sorted_nil.
Qed.