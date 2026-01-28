Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [1; 2; 3; 6; 1; 0; -8; 9; -12; 7; 6; 5; 1; 1] 
  [-8; 2; 3; 1; 1; 0; 1; 9; -12; 6; 6; 5; 7; 1].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 14 (destruct i; [ 
        simpl in H; 
        try (exfalso; apply H; reflexivity); 
        simpl; reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        vm_compute.
        (* Goal: Permutation [-8; 1; 1; 6; 7] [1; 6; -8; 7; 1] *)
        transitivity (-8 :: [1; 6] ++ [7; 1]).
        apply Permutation_cons; [ | apply Permutation_middle ].
        (* Subgoal: Permutation [1; 1; 6; 7] [1; 6; 7; 1] *)
        apply Permutation_cons.
        (* Subgoal: Permutation [1; 6; 7] [6; 7; 1] *)
        transitivity (1 :: [6; 7] ++ []).
        apply Permutation_cons; [ | apply Permutation_middle ].
        (* Subgoal: Permutation [6; 7] [6; 7] *)
        apply Permutation_refl.
      * (* Sorted *)
        vm_compute.
        repeat (apply Sorted_cons; [ 
          match goal with 
          | |- HdRel _ _ [] => apply HdRel_nil 
          | |- _ => apply HdRel_cons; lia 
          end 
        | ]).
        apply Sorted_nil.
Qed.