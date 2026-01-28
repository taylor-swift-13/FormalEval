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
  [300; 500; 6; 8; 289; -105; -277; 11; 3; 4; 5; 700; 900; -901; 800; 1000] 
  [-277; 500; 6; 4; 289; -105; 8; 11; 3; 300; 5; 700; 900; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 17 (destruct i; [
        simpl in *;
        try (exfalso; compute in H; apply H; reflexivity);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-277 :: [300; 8] ++ [4; 900; 1000]).
        { apply Permutation_cons.
          transitivity (4 :: [300; 8] ++ [900; 1000]).
          { apply Permutation_cons.
            transitivity (8 :: [300] ++ [900; 1000]).
            { apply Permutation_cons.
              simpl. apply Permutation_refl. }
            { simpl. apply Permutation_middle. } }
          { simpl. apply Permutation_middle. } }
        { simpl. apply Permutation_middle. }
      * simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; hnf; intro; discriminate); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.