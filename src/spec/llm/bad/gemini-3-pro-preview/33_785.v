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
  [-4; 7; 3; 289; 290; 3; 0; -8; 6; 2; 0; 8; 7; 2; 3; 7] 
  [-4; 7; 3; 0; 290; 3; 2; -8; 6; 7; 0; 8; 7; 2; 3; 289].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 16 (destruct i as [|i]; [ simpl in *; try congruence; try lia | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        apply perm_skip.
        apply Permutation_trans with (l' := [0; 289; 2; 7; 7]).
        { constructor. }
        apply perm_skip.
        apply Permutation_trans with (l' := [2; 289; 7; 7]).
        { constructor. }
        apply perm_skip.
        apply Permutation_trans with (l' := [7; 289; 7]).
        { constructor. }
        apply perm_skip.
        constructor.
      * (* Sorted *)
        simpl.
        repeat constructor; try lia.
Qed.