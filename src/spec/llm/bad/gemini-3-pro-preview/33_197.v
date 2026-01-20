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
  [10; 9; 8; 7; 6; 5; 4; 3; 2; 1; -1; -3; -4; -5; -6; -7; -8; -9; -10]
  [-10; 9; 8; -7; 6; 5; -4; 3; 2; 1; -1; -3; 4; -5; -6; 7; -8; -9; 10].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Unroll the loop for the length of the list *)
      repeat (
        try (simpl; reflexivity); (* Solves the case when list is exhausted *)
        destruct i as [|i]; [
          simpl in H; try (exfalso; apply H; reflexivity); simpl; reflexivity 
        | ]
      ).
    + split.
      * simpl.
        (* Verify that the input thirds are the reverse of the output thirds *)
        assert (Hrev: [10; 7; 4; 1; -4; -7; -10] = rev [-10; -7; -4; 1; 4; 7; 10]) by reflexivity.
        rewrite Hrev.
        apply Permutation_rev.
      * simpl.
        (* Prove sortedness by checking each adjacent pair *)
        repeat (apply Sorted_cons; [ | simpl; constructor; try (unfold Z.le; simpl; discriminate) ]).
        apply Sorted_nil.
Qed.