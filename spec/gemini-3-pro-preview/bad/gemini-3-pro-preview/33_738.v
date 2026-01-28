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
  [500; 6; 7; 1001; 290; 3; 8; 289; 20; 104; -277; 104; 200; 3; 4; -8; 700; -2; -901; 800; 1000]
  [-901; 6; 7; -8; 290; 3; 8; 289; 20; 104; -277; 104; 200; 3; 4; 500; 700; -2; 1001; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [
        simpl; try reflexivity; try (exfalso; compute in H; congruence)
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-901 :: [500; 1001; 8; 104; 200; -8]).
        { apply Permutation_cons.
          transitivity (-8 :: [500; 1001; 8; 104; 200]).
          { apply Permutation_cons.
            transitivity (8 :: [500; 1001; 104; 200]).
            { apply Permutation_cons.
              transitivity (104 :: [500; 1001; 200]).
              { apply Permutation_cons.
                transitivity (200 :: [500; 1001]).
                { apply Permutation_cons.
                  apply Permutation_refl. }
                { apply Permutation_sym. apply Permutation_middle. } }
              { apply Permutation_sym. apply Permutation_middle. } }
            { apply Permutation_sym. apply Permutation_middle. } }
          { apply Permutation_sym. apply Permutation_cons_append. } }
        { apply Permutation_sym. apply Permutation_cons_append. }
      * simpl.
        repeat (constructor; [| simpl; try apply HdRel_nil; constructor; lia]).
        apply Sorted_nil.
Qed.