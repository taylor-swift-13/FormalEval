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

Example test_case : sort_third_spec [5; 2; 7; 9; 3; -7; 11; 8; -6; 0; 1; 6; 19] [0; 2; 7; 5; 3; -7; 9; 8; -6; 11; 1; 6; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Handle the first 13 indices explicitly *)
      do 13 (destruct i; [ simpl in H; try contradiction; simpl; reflexivity | ]).
      (* For i >= 13, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [0; 5; 9; 11; 19] [5; 9; 11; 0; 19] *)
        (* Rewrite RHS to match the form expected by Permutation_middle: l1 ++ x :: l2 *)
        change [5; 9; 11; 0; 19] with ([5; 9; 11] ++ 0 :: [19]).
        apply Permutation_middle.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; simpl; try trivial).
Qed.