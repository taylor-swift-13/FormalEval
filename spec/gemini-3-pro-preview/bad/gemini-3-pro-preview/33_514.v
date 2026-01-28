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
  [-4; 8; 3; -6; 3; 0; 7; -8; -7; 2; 0; 0; 1; -7; 20; 0; 0; -7]
  [-6; 8; 3; -4; 3; 0; 0; -8; -7; 1; 0; 0; 2; -7; 20; 7; 0; -7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Check for i from 0 to 18. Indices divisible by 3 result in contradiction in H. *)
      do 19 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        (* Goal: Permutation [-6; -4; 0; 1; 2; 7] [-4; -6; 7; 2; 1; 0] *)
        eapply perm_trans.
        2: apply perm_swap. (* Swaps -4 and -6 in RHS to match LHS prefix *)
        apply perm_skip. apply perm_skip.
        (* Goal: Permutation [0; 1; 2; 7] [7; 2; 1; 0] *)
        assert (Hrev: [7; 2; 1; 0] = rev [0; 1; 2; 7]) by reflexivity.
        rewrite Hrev.
        apply Permutation_rev.
      * simpl.
        repeat (apply Sorted_cons; [ 
          (apply HdRel_cons; vm_compute; try discriminate) || apply HdRel_nil 
        | ]).
        apply Sorted_nil.
Qed.