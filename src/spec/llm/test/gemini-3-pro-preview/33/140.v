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
  [19; 0; -901; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 21; 20] 
  [2; 0; -901; 5; 3; 4; 8; 6; 7; 11; 9; 10; 14; 12; 13; 17; 15; 16; 19; 18; 19; 21; 20].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 25 (destruct i; [ simpl in *; try (contradict H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [2; 5; 8; 11; 14; 17; 19; 21] with ([2; 5; 8; 11; 14; 17] ++ 19 :: [21]).
        change [19; 2; 5; 8; 11; 14; 17; 21] with (19 :: [2; 5; 8; 11; 14; 17] ++ [21]).
        apply Permutation_sym.
        apply Permutation_middle.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; first [ apply HdRel_nil | apply HdRel_cons; compute; discriminate ] ]).
        apply Sorted_nil.
Qed.