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
  [9; 12; 3; 6; 15; 0; -3; 1000; 18; 21; 30; -9] 
  [-3; 12; 3; 6; 15; 0; 9; 1000; 18; 21; 30; -9].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 12 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* LHS: [-3; 6; 9; 21] *)
        (* RHS: [9; 6; -3; 21] *)
        apply Permutation_trans with (l' := [-3; 9; 6; 21]).
        -- apply Permutation_cons. apply Permutation_swap.
        -- apply Permutation_sym.
           apply Permutation_trans with (l' := [9; -3; 6; 21]).
           ++ apply Permutation_swap.
           ++ apply Permutation_cons. apply Permutation_swap.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [| constructor; vm_compute; try (intro C; discriminate) ]).
        apply Sorted_nil.
Qed.