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
  [19; 0; -901; 2; 3; 4; 5; 6; 7; 8; 10; 11; 12; 14; 14; 15; 16; 17; 18; 19; 21; 20] 
  [2; 0; -901; 5; 3; 4; 8; 6; 7; 12; 10; 11; 15; 14; 14; 18; 16; 17; 19; 19; 21; 20].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [
        simpl in *;
        try (exfalso; vm_compute in H; congruence);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        change [2; 5; 8; 12; 15; 18; 19; 20] with ([2; 5; 8; 12; 15; 18] ++ 19 :: [20]).
        apply Permutation_cons_app with (l1 := [2; 5; 8; 12; 15; 18]) (l2 := [20]).
        simpl. reflexivity.
      * simpl.
        repeat (constructor; simpl; try (vm_compute; congruence)).
Qed.