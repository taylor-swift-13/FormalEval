Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [9; 12; 3; 6; 15; 0; -3; -6; 18; 29; 21; 30; -9; 3] 
  [-9; 12; 3; -3; 15; 0; 6; -6; 18; 9; 21; 30; 29; 3].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl in *; try reflexivity; try (contradict H; discriminate) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply perm_trans.
        2: apply Permutation_cons_app.
        apply perm_skip.
        eapply perm_trans.
        2: apply Permutation_middle.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (constructor; try lia).
Qed.