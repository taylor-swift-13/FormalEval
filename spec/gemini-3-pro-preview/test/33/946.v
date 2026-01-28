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
  [5; 2; 7; 9; 3; -6; 9; 11; 8; 0; 300; 1; 13; 6; -2; 19] 
  [0; 2; 7; 5; 3; -6; 9; 11; 8; 9; 300; 1; 13; 6; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 16 (destruct i; [ 
        simpl in *; 
        try (exfalso; compute in H; congruence);
        try reflexivity 
        | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        change [0; 5; 9; 9; 13; 19] with (0 :: [5; 9; 9] ++ [13; 19]).
        change [5; 9; 9; 0; 13; 19] with ([5; 9; 9] ++ 0 :: [13; 19]).
        apply Permutation_middle.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; simpl; try discriminate).
Qed.