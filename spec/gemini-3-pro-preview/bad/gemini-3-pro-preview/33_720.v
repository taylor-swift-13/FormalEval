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
  [300; 500; 6; 104; 7; 8; 289; 20; -105; -277; 104; 8; 9; 3; 4; 5; 700; 900; -200; -901; 800; 1000] 
  [-277; 500; 6; -200; 7; 8; 5; 20; -105; 9; 104; 8; 104; 3; 4; 289; 700; 900; 300; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ simpl in *; try reflexivity; try contradiction | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply Permutation_trans with (l' := [300; 104; 289] ++ -277 :: [9; 5; -200; 1000]); [ apply Permutation_cons_app | reflexivity ].
        eapply Permutation_trans with (l' := [300; 104; 289; 9; 5] ++ -200 :: [1000]); [ apply Permutation_cons_app | reflexivity ].
        eapply Permutation_trans with (l' := [300; 104; 289; 9] ++ 5 :: [1000]); [ apply Permutation_cons_app | reflexivity ].
        eapply Permutation_trans with (l' := [300; 104; 289] ++ 9 :: [1000]); [ apply Permutation_cons_app | reflexivity ].
        eapply Permutation_trans with (l' := [300] ++ 104 :: [289; 1000]); [ apply Permutation_cons_app | reflexivity ].
        eapply Permutation_trans with (l' := [300] ++ 289 :: [1000]); [ apply Permutation_cons_app | reflexivity ].
        eapply Permutation_trans with (l' := [] ++ 300 :: [1000]); [ apply Permutation_cons_app | reflexivity ].
        eapply Permutation_trans with (l' := [] ++ 1000 :: []); [ apply Permutation_cons_app | reflexivity ].
        apply Permutation_nil.
      * simpl.
        repeat (constructor; try (vm_compute; reflexivity)).
Qed.