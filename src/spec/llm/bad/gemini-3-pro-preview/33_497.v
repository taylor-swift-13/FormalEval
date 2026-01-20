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
  [9; 0; 13; 3; 4; -4; 9; -5; 289; 12; 3] 
  [3; 0; 13; 9; 4; -4; 9; -5; 289; 12; 3].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length *)
    simpl. reflexivity.
  - split.
    + (* 2. indices *)
      intros i H.
      do 12 (destruct i; [ simpl in H; try lia; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation *)
        simpl.
        apply Permutation_swap.
        apply Permutation_refl.
      * (* 4. Sorted *)
        simpl.
        repeat (constructor; simpl; try lia).
Qed.