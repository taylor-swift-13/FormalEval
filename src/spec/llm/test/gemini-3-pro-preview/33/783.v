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
  [5; 2; 7; 9; 3; -7; 11; 8; 0; -8; 1; 13; 6; -2; 19; 13]
  [-8; 2; 7; 5; 3; -7; 6; 8; 0; 9; 1; 13; 11; -2; 19; 13].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [simpl in *; try (elim H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        eapply Permutation_trans with (l' := [5; 9; -8; 11; 6; 13]).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        eapply Permutation_trans with (l' := [5; -8; 9; 11; 6; 13]).
        { apply perm_skip. apply perm_swap. }
        eapply Permutation_trans with (l' := [-8; 5; 9; 11; 6; 13]).
        { apply perm_swap. }
        apply perm_skip. apply perm_skip.
        eapply Permutation_trans with (l' := [9; 6; 11; 13]).
        { apply perm_skip. apply perm_swap. }
        eapply Permutation_trans with (l' := [6; 9; 11; 13]).
        { apply perm_swap. }
        apply Permutation_refl.
      * simpl.
        repeat (constructor; try (unfold Z.le; simpl; discriminate)).
Qed.