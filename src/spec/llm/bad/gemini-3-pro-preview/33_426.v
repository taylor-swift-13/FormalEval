Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
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
  [19; 0; 2; 4; 3; 4; 5; 6; 7; -9; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 11; 16; 11]
  [-9; 0; 2; 4; 3; 4; 5; 6; 7; 11; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 19; 11; 16; 20].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 25 (destruct i as [|i]; [
        try (exfalso; apply H; reflexivity);
        simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (-9 :: 19 :: 4 :: 5 :: 11 :: 14 :: 17 :: 20 :: 11 :: nil).
        2: change (19 :: 4 :: 5 :: -9 :: 11 :: 14 :: 17 :: 20 :: 11 :: []) with ([19; 4; 5] ++ -9 :: [11; 14; 17; 20; 11]); apply Permutation_middle.
        apply Permutation_cons.
        
        apply Permutation_trans with (4 :: 19 :: 5 :: 11 :: 14 :: 17 :: 20 :: 11 :: nil).
        2: change (19 :: 4 :: 5 :: 11 :: 14 :: 17 :: 20 :: 11 :: []) with ([19] ++ 4 :: [5; 11; 14; 17; 20; 11]); apply Permutation_middle.
        apply Permutation_cons.
        
        apply Permutation_trans with (5 :: 19 :: 11 :: 14 :: 17 :: 20 :: 11 :: nil).
        2: change (19 :: 5 :: 11 :: 14 :: 17 :: 20 :: 11 :: []) with ([19] ++ 5 :: [11; 14; 17; 20; 11]); apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_trans with (11 :: 19 :: 14 :: 17 :: 20 :: 11 :: nil).
        2: change (19 :: 11 :: 14 :: 17 :: 20 :: 11 :: []) with ([19] ++ 11 :: [14; 17; 20; 11]); apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_trans with (11 :: 19 :: 14 :: 17 :: 20 :: nil).
        2: change (19 :: 14 :: 17 :: 20 :: 11 :: []) with ([19; 14; 17; 20] ++ 11 :: []); apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_trans with (14 :: 19 :: 17 :: 20 :: nil).
        2: change (19 :: 14 :: 17 :: 20 :: []) with ([19] ++ 14 :: [17; 20]); apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_trans with (17 :: 19 :: 20 :: nil).
        2: change (19 :: 17 :: 20 :: []) with ([19] ++ 17 :: [20]); apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_refl.

      * simpl.
        repeat (apply Sorted_cons; [ | apply Z.leb_le; reflexivity ]).
        apply Sorted_nil.
Qed.