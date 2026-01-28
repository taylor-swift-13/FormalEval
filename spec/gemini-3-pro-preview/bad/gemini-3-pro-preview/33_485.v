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
  [-4; 7; 3; -6; 3; -1; 0; 7; -8; -7; 2; 0; 1; 20; 0; 0] 
  [-7; 7; 3; -6; 3; -1; -4; 7; -8; 0; 2; 0; 0; 20; 0; 1].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Check each index up to the length of the list *)
      do 16 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      (* For indices beyond the list length, both are None *)
      simpl. reflexivity.
    + split.
      * (* Permutation proof *)
        vm_compute.
        (* Goal: Permutation [-7; -6; -4; 0; 0; 1] [-4; -6; 0; -7; 1; 0] *)
        apply Permutation_trans with (l' := -7 :: [-4; -6; 0; 1; 0]).
        2: { 
          apply Permutation_sym.
          change [-4; -6; 0; -7; 1; 0] with ([-4; -6; 0] ++ -7 :: [1; 0]).
          apply Permutation_middle.
        }
        constructor.
        (* Goal: Permutation [-6; -4; 0; 0; 1] [-4; -6; 0; 1; 0] *)
        apply Permutation_trans with (l' := -6 :: [-4; 0; 1; 0]).
        2: {
          apply Permutation_sym.
          change [-4; -6; 0; 1; 0] with ([-4] ++ -6 :: [0; 1; 0]).
          apply Permutation_middle.
        }
        constructor.
        (* Goal: Permutation [-4; 0; 0; 1] [-4; 0; 1; 0] *)
        constructor.
        (* Goal: Permutation [0; 0; 1] [0; 1; 0] *)
        constructor.
        (* Goal: Permutation [0; 1] [1; 0] *)
        apply perm_swap.
      * (* Sorted proof *)
        vm_compute.
        repeat (constructor; simpl; try easy).
Qed.