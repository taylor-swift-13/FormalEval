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
  [1; 2; 3; -7; -3; 5; 0; -8; -7; 9; -12; 7; 6] 
  [-7; 2; 3; 0; -3; 5; 1; -8; -7; 6; -12; 7; 9].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i as [|i]; [
        simpl in *;
        match goal with
        | [ H : (_ mod 3 <> 0)%nat |- _ ] =>
            try (exfalso; compute in H; congruence);
            try reflexivity
        end
        | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_trans with (-7 :: 1 :: 0 :: 6 :: 9).
        { apply Permutation_cons. apply Permutation_swap. }
        apply perm_trans with (1 :: -7 :: 0 :: 6 :: 9).
        { apply Permutation_swap. }
        apply Permutation_cons. apply Permutation_cons. apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [| apply HdRel_cons; compute; intro Hc; discriminate || apply HdRel_nil]).
        apply Sorted_nil.
Qed.