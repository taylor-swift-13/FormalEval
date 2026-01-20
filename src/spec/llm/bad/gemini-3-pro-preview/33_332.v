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

Example test_case : sort_third_spec [9; 0; 8; -1; 6; -4; -5; 12; 18; 12] [-5; 0; 8; -1; 6; -4; 9; 12; 18; 12].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 10 (destruct i; [ simpl in *; try (exfalso; lia); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [-5; -1; 9; 12] [9; -1; -5; 12] *)
        apply Permutation_trans with (l' := [-5; 9; -1; 12]).
        -- apply Permutation_cons. apply Permutation_swap.
        -- apply Permutation_trans with (l' := [9; -5; -1; 12]).
           ++ apply Permutation_swap.
           ++ apply Permutation_cons. apply Permutation_swap.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ try (apply HdRel_cons; lia); try apply HdRel_nil | ]).
        apply Sorted_nil.
Qed.