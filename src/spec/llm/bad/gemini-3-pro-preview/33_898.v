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
  [300; 500; 6; 7; 290; 300; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 8; 900; -901; 800; 1000; -901; 1000]
  [-901; 500; 6; -901; 290; 300; -105; 289; 20; 7; -277; 104; 8; 3; 4; 200; 8; 900; 300; 800; 1000; 700; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply Permutation_trans.
        2: { change [300; 7; 8; -105; 200; 700; -901; -901] with ([300; 7; 8; -105; 200; 700; -901] ++ [-901] ++ []).
             apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        eapply Permutation_trans.
        2: { change [300; 7; 8; -105; 200; 700; -901] with ([300; 7; 8; -105; 200; 700] ++ [-901] ++ []).
             apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        eapply Permutation_trans.
        2: { change [300; 7; 8; -105; 200; 700] with ([300; 7; 8] ++ [-105] ++ [200; 700]).
             apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        eapply Permutation_trans.
        2: { change [300; 7; 8; 200; 700] with ([300] ++ [7] ++ [8; 200; 700]).
             apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        eapply Permutation_trans.
        2: { change [300; 8; 200; 700] with ([300] ++ [8] ++ [200; 700]).
             apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        eapply Permutation_trans.
        2: { change [300; 200; 700] with ([300] ++ [200] ++ [700]).
             apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        apply Sorted_cons. apply HdRel_cons. apply Z.le_refl.
        apply Sorted_cons. apply HdRel_cons. compute. intro; discriminate.
        apply Sorted_cons. apply HdRel_cons. compute. intro; discriminate.
        apply Sorted_cons. apply HdRel_cons. compute. intro; discriminate.
        apply Sorted_cons. apply HdRel_cons. compute. intro; discriminate.
        apply Sorted_cons. apply HdRel_cons. compute. intro; discriminate.
        apply Sorted_cons. apply HdRel_cons. compute. intro; discriminate.
        apply Sorted_cons. apply HdRel_nil.
        apply Sorted_nil.
Qed.