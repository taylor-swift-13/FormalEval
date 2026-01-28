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

Example test_case : sort_third_spec [-4; 8; 3; -6; 3; 0; -8; 6; 2; 1; 800; 0; 800] [-8; 8; 3; -6; 3; 0; -4; 6; 2; 1; 800; 0; 800].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *) reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* We destruct i enough times to cover the list *)
      do 14 (destruct i; [ 
        vm_compute in H |- *; 
        try (exfalso; apply H; reflexivity); 
        reflexivity 
      | ]).
      (* Out of bounds *)
      reflexivity.
    + split.
      * (* Permutation *)
        vm_compute.
        (* Goal: Permutation [-8; -6; -4; 1; 800] [-4; -6; -8; 1; 800] *)
        change [-8; -6; -4; 1; 800] with ([-8; -6; -4] ++ [1; 800]).
        change [-4; -6; -8; 1; 800] with ([-4; -6; -8] ++ [1; 800]).
        apply Permutation_app_tail.
        apply Permutation_rev.
      * (* Sorted *)
        vm_compute.
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; simpl; lia) ]).
        apply Sorted_nil.
Qed.