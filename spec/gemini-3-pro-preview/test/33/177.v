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

Example test_case : sort_third_spec [9; 0; 8; -1; 6; -4; -5; 12; 0] [-5; 0; 8; -1; 6; -4; 9; 12; 0].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 9 (destruct i; [ simpl in H; try (exfalso; apply H; reflexivity); reflexivity | ]).
      reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (l' := [-5; 9; -1]).
        -- constructor 2. constructor 3.
        -- apply Permutation_trans with (l' := [9; -5; -1]).
           ++ constructor 3.
           ++ constructor 2. constructor 3.
      * simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ apply HdRel_cons. vm_compute. discriminate.
        -- apply HdRel_cons. vm_compute. discriminate.
Qed.