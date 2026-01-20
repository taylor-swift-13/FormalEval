Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [-4; 7; 3; -5; 200; -8; -7; 2; 0; 1; 8; 0; -6] 
  [-7; 7; 3; -6; 200; -8; -5; 2; 0; -4; 8; 0; 1].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 14 (destruct i as [|i]; [
        simpl in *; try congruence; try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-7 :: [-4; -5] ++ [1; -6]).
        { apply Permutation_middle. }
        simpl. apply perm_skip.
        transitivity (-6 :: [-4; -5; 1] ++ []).
        { rewrite <- app_nil_r. apply Permutation_middle. }
        simpl. apply perm_skip.
        transitivity (-5 :: [-4] ++ [1]).
        { apply Permutation_middle. }
        simpl. apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ try (apply HdRel_cons; lia); try apply HdRel_nil | ]).
        apply Sorted_nil.
Qed.