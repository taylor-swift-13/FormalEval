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
  [9; -1; 700; -1; 6; -4; 3; 20; 11; 17; 3; -1] 
  [-1; -1; 700; 3; 6; -4; 9; 20; 11; 17; 3; -1].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 12 (destruct i; [ simpl in *; try reflexivity; exfalso; apply H; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_trans with (l' := [-1; 9; 3; 17]).
        -- apply perm_skip. apply perm_swap.
        -- apply perm_swap.
      * simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_nil. }
              { apply HdRel_nil. } }
            { apply HdRel_cons. apply Z.leb_le. vm_compute. reflexivity. } }
          { apply HdRel_cons. apply Z.leb_le. vm_compute. reflexivity. } }
        { apply HdRel_cons. apply Z.leb_le. vm_compute. reflexivity. }
Qed.