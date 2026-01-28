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
  [300; 500; 6; 7; -901; 8; 289; -105; -277; 5; 200; 3; 4; 5; 700; 900; -901; 800; 1000; 801]
  [4; 500; 6; 5; -901; 8; 7; -105; -277; 289; 200; 3; 300; 5; 700; 900; -901; 800; 1000; 801].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [ simpl; try (exfalso; apply H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * vm_compute extract_thirds.
        apply Permutation_sym.
        assert (H4: Permutation [300; 7; 289; 5; 4; 900; 1000] (4 :: [300; 7; 289; 5; 900; 1000])).
        { apply Permutation_sym. apply Permutation_cons_app with (l1:=[300; 7; 289; 5]) (l2:=[900; 1000]). reflexivity. }
        rewrite H4; clear H4. apply Permutation_cons.
        assert (H5: Permutation [300; 7; 289; 5; 900; 1000] (5 :: [300; 7; 289; 900; 1000])).
        { apply Permutation_sym. apply Permutation_cons_app with (l1:=[300; 7; 289]) (l2:=[900; 1000]). reflexivity. }
        rewrite H5; clear H5. apply Permutation_cons.
        assert (H7: Permutation [300; 7; 289; 900; 1000] (7 :: [300; 289; 900; 1000])).
        { apply Permutation_sym. apply Permutation_cons_app with (l1:=[300]) (l2:=[289; 900; 1000]). reflexivity. }
        rewrite H7; clear H7. apply Permutation_cons.
        apply Permutation_swap.
      * vm_compute extract_thirds.
        repeat (apply Sorted_cons; [ simpl; try lia | ]).
        apply Sorted_nil.
Qed.