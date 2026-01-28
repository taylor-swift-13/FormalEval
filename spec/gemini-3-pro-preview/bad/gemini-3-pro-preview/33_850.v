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
  [5%Z; 2%Z; 7%Z; -1%Z; 9%Z; 0%Z; 3%Z; -6%Z; 9%Z; 11%Z; 8%Z; -6%Z; 0%Z; 300%Z; 1%Z; 13%Z; 6%Z; -2%Z; 19%Z]
  [-1%Z; 2%Z; 7%Z; 0%Z; 9%Z; 0%Z; 3%Z; -6%Z; 9%Z; 5%Z; 8%Z; -6%Z; 11%Z; 300%Z; 1%Z; 13%Z; 6%Z; -2%Z; 19%Z].
Proof.
  unfold sort_third_spec.
  split.
  - reflexivity.
  - split.
    + intros i H.
      do 19 (destruct i; [ vm_compute in H; try congruence; vm_compute; reflexivity | ]).
      vm_compute. reflexivity.
    + split.
      * vm_compute. apply Permutation_refl.
      * vm_compute.
        repeat (apply Sorted_cons; [ | constructor; try reflexivity ]).
        apply Sorted_nil.
Qed.