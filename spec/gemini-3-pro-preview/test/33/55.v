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
  [3; 1; 2; 3; 4; 5; 6; 7; 45; 9; 12; 14; 15; 21; 3; 13] 
  [3; 1; 2; 3; 4; 5; 6; 7; 45; 9; 12; 14; 13; 21; 3; 15].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We unroll the loop for the finite list length (16 elements) *)
      do 17 (destruct i as [|i]; [
        simpl in H; try congruence; simpl; reflexivity
      | ]).
      (* Case i >= 17, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* The lists are [3; 3; 6; 9; 13; 15] and [3; 3; 6; 9; 15; 13] *)
        repeat apply perm_skip.
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try apply HdRel_cons; unfold Z.le; simpl; discriminate ]).
        apply Sorted_nil.
Qed.