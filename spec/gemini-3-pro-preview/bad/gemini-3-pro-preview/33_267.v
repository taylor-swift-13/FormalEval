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
  [-4; 7; 3; 105; 0; -8; 7; 2; 1; 8; 14; 0; 6; -8] 
  [-4; 7; 3; 6; 0; -8; 7; 2; 1; 8; 14; 0; 105; -8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 14 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        apply Permutation_sym.
        change [105; 7; 8; 6] with ([105; 7; 8] ++ [6]).
        apply Permutation_trans with (l' := [6] ++ [105; 7; 8]).
        { apply Permutation_app_comm. }
        simpl.
        apply Permutation_cons.
        change [105; 7; 8] with ([105] ++ [7; 8]).
        apply Permutation_trans with (l' := [7; 8] ++ [105]).
        { apply Permutation_app_comm. }
        simpl. apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| try apply HdRel_nil; apply HdRel_cons; vm_compute; reflexivity]).
        apply Sorted_nil.
Qed.