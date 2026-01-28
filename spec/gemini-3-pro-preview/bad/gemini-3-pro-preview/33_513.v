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
  [300; 500; 6; 7; 8; 1001; 20; -105; -277; 104; 200; 3; 105; 4; 5; 700; 900; -200; -901; 800; 1000; 22; 6]
  [-901; 500; 6; 7; 8; 1001; 20; -105; -277; 22; 200; 3; 104; 4; 5; 105; 900; -200; 300; 800; 1000; 700; 6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ simpl in *; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (-901 :: [300; 7; 20; 104; 105; 700; 22]).
        { apply Permutation_cons.
          apply Permutation_trans with (7 :: [300; 20; 104; 105; 700; 22]).
          { apply Permutation_cons.
            apply Permutation_trans with (20 :: [300; 104; 105; 700; 22]).
            { apply Permutation_cons.
              apply Permutation_trans with (22 :: [300; 104; 105; 700]).
              { apply Permutation_cons.
                apply Permutation_trans with (104 :: [300; 105; 700]).
                { apply Permutation_cons.
                  apply Permutation_trans with (105 :: [300; 700]).
                  { apply Permutation_cons.
                    apply Permutation_cons.
                    apply Permutation_refl. }
                  apply Permutation_middle. }
                apply Permutation_middle. }
              apply Permutation_middle. }
            apply Permutation_middle. }
          apply Permutation_middle. }
        apply Permutation_middle.
      * simpl. repeat constructor.
Qed.