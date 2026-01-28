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
  [-4; 7; 3; 289; 290; 3; 0; -8; 6; 2; 0; 1; -9; 8] 
  [-9; 7; 3; -4; 290; 3; 0; -8; 6; 2; 0; 1; 289; 8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 14 (destruct i; [ simpl in H; try congruence; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-9 :: [-4; 289; 0; 2]).
        { apply perm_skip. apply perm_skip.
          apply Permutation_sym.
          change [0; 2; 289] with ([0; 2] ++ [289]).
          apply Permutation_middle. }
        { change [-4; 289; 0; 2; -9] with ([-4; 289; 0; 2] ++ [-9]).
          apply Permutation_middle. }
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; apply Z.leb_le; reflexivity ]).
        apply Sorted_nil.
        apply HdRel_nil.
Qed.