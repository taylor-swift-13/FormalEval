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
  [1; 15; 2; 3; 4; 5; 19; 6; 7; 8; 10; 1000; 12; 13; 14; 15; 16; 17; 18; 20; 20; 7; 8]
  [1; 15; 2; 3; 4; 5; 7; 6; 7; 8; 10; 1000; 12; 13; 14; 15; 16; 17; 18; 20; 20; 19; 8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [
        simpl;
        match goal with
        | [ |- Some ?x = Some ?x ] => reflexivity
        | _ => exfalso; apply H; vm_compute; reflexivity
        end
      | ]).
      simpl. reflexivity.
    + split.
      * vm_compute.
        apply Permutation_cons. apply Permutation_cons.
        transitivity (7 :: [19; 8; 12; 15; 18]).
        -- apply Permutation_cons.
           apply perm_swap. apply Permutation_cons.
           apply perm_swap. apply Permutation_cons.
           apply perm_swap. apply Permutation_cons.
           apply perm_swap. apply Permutation_refl.
        -- change [19; 8; 12; 15; 18; 7] with ([19; 8; 12; 15; 18] ++ [7]).
           apply Permutation_middle.
      * vm_compute.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- repeat (apply HdRel_cons; unfold Z.le; simpl; discriminate).
Qed.