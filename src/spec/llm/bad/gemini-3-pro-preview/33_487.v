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
  [-4; 8; 3; -6; 3; 0; 7; -8; -7; 2; 0; 1; 20; 0; 0] 
  [-6; 8; 3; -4; 3; 0; 2; -8; -7; 7; 0; 1; 20; 0; 0].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl in *; try reflexivity; try (exfalso; vm_compute in H; discriminate) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_trans with (l' := [-6; -4; 7; 2; 20]).
        -- apply perm_skip. apply perm_skip. apply perm_swap.
        -- apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; apply Z.leb_le; vm_compute; reflexivity ] ]).
        apply Sorted_nil.
Qed.