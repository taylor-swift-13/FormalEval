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

Example test_case : sort_third_spec [2; 2; 35; 1; 3; 7; 8; 9; 10] [1; 2; 35; 2; 3; 7; 8; 9; 10].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* We destruct i enough times to cover the list length. 
         For indices where i mod 3 = 0, H provides a contradiction.
         For other indices, the values match by computation. *)
      do 9 (destruct i; [
        simpl in *; try (exfalso; apply H; reflexivity); try reflexivity |
      ]).
      (* For i >= 9, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [1; 2; 8] [2; 1; 8] *)
        (* This matches the swap constructor exactly: 1 :: 2 :: [8] vs 2 :: 1 :: [8] *)
        apply perm_swap.
      * (* Sorted *)
        simpl.
        (* Goal: Sorted Z.le [1; 2; 8] *)
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_nil. }
            { apply HdRel_nil. } }
          { apply HdRel_cons. auto with zarith. } }
        { apply HdRel_cons. auto with zarith. }
Qed.