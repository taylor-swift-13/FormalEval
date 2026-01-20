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
  [-4; 7; 3; -6; 3; 0; -8; 5; 2; 0; 1; 8; 14; 0] 
  [-8; 7; 3; -6; 3; 0; -4; 5; 2; 0; 1; 8; 14; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for each index up to list length *)
      do 15 (destruct i as [|i]; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Input extracted: [-4; -6; -8; 0; 14] *)
        (* Output extracted: [-8; -6; -4; 0; 14] *)
        (* Target: Permutation [-8; -6; -4; 0; 14] [-4; -6; -8; 0; 14] *)
        apply Permutation_trans with (l' := [-6; -8; -4; 0; 14]).
        { apply perm_swap. }
        apply Permutation_trans with (l' := [-6; -4; -8; 0; 14]).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; apply Z.leb_le; reflexivity) ]).
        apply Sorted_nil.
Qed.