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
  [-4; 7; -6; 3; 0; -8; 6; 2; 0; 1; 8; 0; 3] 
  [-4; 7; -6; 1; 0; -8; 3; 2; 0; 3; 8; 0; 6].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Destruct i enough times to cover the concrete list length (13 elements) *)
      do 14 (destruct i as [|i]; [ simpl in *; try reflexivity; try (exfalso; compute in H; congruence) | ]).
      (* For indices beyond the list length, both nth_errors are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-4; 1; 3; 3; 6] [-4; 3; 6; 1; 3] *)
        apply Permutation_cons.
        (* Goal: Permutation [1; 3; 3; 6] [3; 6; 1; 3] *)
        eapply Permutation_trans.
        2: { apply Permutation_swap. } (* -> [6; 3; 1; 3] *)
        eapply Permutation_trans.
        2: { apply Permutation_cons. apply Permutation_swap. } (* -> [6; 1; 3; 3] *)
        eapply Permutation_trans.
        2: { apply Permutation_swap. } (* -> [1; 6; 3; 3] *)
        apply Permutation_cons.
        (* Goal: Permutation [3; 3; 6] [6; 3; 3] *)
        eapply Permutation_trans.
        2: { apply Permutation_swap. } (* -> [3; 6; 3] *)
        apply Permutation_cons.
        (* Goal: Permutation [3; 6] [6; 3] *)
        apply Permutation_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try apply HdRel_cons; auto with zarith ]).
        apply Sorted_nil.
Qed.