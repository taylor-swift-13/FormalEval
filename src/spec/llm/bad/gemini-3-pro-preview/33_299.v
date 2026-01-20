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
  [1; 2; 3; 5; 1; 16; -11; 16; -8; 9; -12; 7; 6; -12; 16] 
  [-11; 2; 3; 1; 1; 16; 5; 16; -8; 6; -12; 7; 9; -12; 16].
Proof.
  unfold sort_third_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Indices not divisible by 3 *)
      intros i H.
      do 15 (destruct i; [ simpl in *; try (contradiction || reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        vm_compute extract_thirds.
        apply Permutation_cons_app with (l1 := [1; 5]) (l2 := [9; 6]).
        { simpl. reflexivity. }
        simpl.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_swap.
        apply Permutation_refl.
      * (* Sorted *)
        vm_compute extract_thirds.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons. apply Z.leb_le. reflexivity.
        -- apply HdRel_cons. apply Z.leb_le. reflexivity.
        -- apply HdRel_cons. apply Z.leb_le. reflexivity.
        -- apply HdRel_cons. apply Z.leb_le. reflexivity.
Qed.