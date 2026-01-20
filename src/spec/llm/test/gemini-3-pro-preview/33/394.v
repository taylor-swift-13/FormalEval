Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [9; -5; 0; -1; 6; -4; -5; 3; 3; 12; 0] 
  [-5; -5; 0; -1; 6; -4; 9; 3; 3; 12; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Destruct i enough times to cover the list length (11 elements) *)
      do 11 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); reflexivity | ]).
      (* For i >= 11, both nth_error return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-5; -1; 9; 12] [9; -1; -5; 12] *)
        apply Permutation_trans with (l' := [-1; -5; 9; 12]).
        { apply perm_swap. }
        apply Permutation_trans with (l' := [-1; 9; -5; 12]).
        { apply perm_skip. apply perm_swap. }
        { apply perm_swap. }
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; simpl; lia) ]).
        apply Sorted_nil.
Qed.