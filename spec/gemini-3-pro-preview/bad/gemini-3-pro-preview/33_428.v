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
  [300%Z; 499%Z; 6%Z; 17%Z; 8%Z; 289%Z; 20%Z; -105%Z; -277%Z; 104%Z; 200%Z; 3%Z; 0%Z; 5%Z; 700%Z; 900%Z; 18%Z; -901%Z; 800%Z; 1000%Z; 0%Z; -277%Z]
  [-277%Z; 499%Z; 6%Z; 0%Z; 8%Z; 289%Z; 17%Z; -105%Z; -277%Z; 20%Z; 200%Z; 3%Z; 104%Z; 5%Z; 700%Z; 300%Z; 18%Z; -901%Z; 800%Z; 1000%Z; 0%Z; 900%Z].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i as [|i]; [
        simpl in *;
        try (compute in H; contradiction);
        try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        repeat (apply Permutation_Add; repeat (constructor || apply Add_cons)).
        apply Permutation_nil.
      * simpl. repeat (constructor; simpl; try (compute; discriminate)).
Qed.