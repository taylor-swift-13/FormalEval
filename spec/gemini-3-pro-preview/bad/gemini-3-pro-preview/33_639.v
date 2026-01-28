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
  [1; 2; 3; 4; 5; 6; 7; 8; -901; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 20; 7; 8] 
  [1; 2; 3; 4; 5; 6; 7; 8; -901; 8; 11; 12; 10; 14; 15; 13; 17; 18; 16; 20; 7; 20].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 22 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        repeat apply Permutation_cons.
        apply perm_trans with (l' := [10; 8; 13; 16; 20]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (l' := [13; 8; 16; 20]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (l' := [16; 8; 20]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (l' := [20; 8]).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_refl.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_nil || (apply HdRel_cons; unfold Z.le; simpl; discriminate) | ]).
        apply Sorted_nil.
Qed.