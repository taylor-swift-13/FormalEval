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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; -199; 200; 3; 4; 5; 700; 900; -200; -901; 800; 1000]
  [-901; 500; 6; 3; 8; 289; 7; -105; -277; 20; -199; 200; 104; 4; 5; 300; 900; -200; 700; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Destruct i 21 times to handle elements within the list bounds *)
      do 21 (destruct i; [ simpl in *; try reflexivity; try contradiction | ]).
      (* Handle out of bounds indices *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Prove Permutation by moving elements to the front one by one *)
        transitivity (-901 :: [300; 7; 20; 104; 3; 700] ++ []).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (3 :: [300; 7; 20; 104] ++ [700]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (7 :: [300] ++ [20; 104; 700]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (20 :: [300] ++ [104; 700]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (104 :: [300] ++ [700]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat constructor; try (simpl; lia).
Qed.