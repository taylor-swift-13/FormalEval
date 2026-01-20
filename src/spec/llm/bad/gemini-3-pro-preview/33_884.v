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
  [500; 6; 7; 290; 3; 8; 289; 20; 104; -277; 200; 3; 4; -8; 700; -2; -901; 800; 1000]
  [-277; 6; 7; -2; 3; 8; 4; 20; 104; 289; 200; 3; 290; -8; 700; 500; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i as [|i]; [ 
        simpl in *; 
        try (exfalso; apply H; reflexivity); 
        reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply Permutation_trans. 2: { apply (Permutation_middle (-277)). } apply Permutation_cons.
        eapply Permutation_trans. 2: { apply (Permutation_middle (-2)). } apply Permutation_cons.
        eapply Permutation_trans. 2: { apply (Permutation_middle 4). } apply Permutation_cons.
        eapply Permutation_trans. 2: { apply (Permutation_middle 289). } apply Permutation_cons.
        eapply Permutation_trans. 2: { apply (Permutation_middle 290). } apply Permutation_cons.
        eapply Permutation_trans. 2: { apply (Permutation_middle 500). } apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; vm_compute; reflexivity | ]).
        apply Sorted_nil.
Qed.