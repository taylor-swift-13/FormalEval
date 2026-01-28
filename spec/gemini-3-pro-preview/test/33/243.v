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
  [900; 2; 7; 11; 9; 3; -7; 8; 0; 1; -12; 6; -2; 19; 13] 
  [-7; 2; 7; -2; 9; 3; 1; 8; 0; 11; -12; 6; 900; 19; 13].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [900; 11; -7; 1; -2] with ([900; 11] ++ -7 :: [1; -2]).
        apply Permutation_cons_app.
        simpl.
        change [900; 11; 1; -2] with ([900; 11; 1] ++ -2 :: []).
        apply Permutation_cons_app.
        simpl.
        change [900; 11; 1] with ([900; 11] ++ 1 :: []).
        apply Permutation_cons_app.
        simpl.
        change [900; 11] with ([900] ++ 11 :: []).
        apply Permutation_cons_app.
        simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; constructor; unfold Z.le; simpl; discriminate]).
        apply Sorted_nil.
Qed.