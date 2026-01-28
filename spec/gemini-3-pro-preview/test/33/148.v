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
  [300; 500; 6; 7; 8; 289; 21; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -901; 800; 1000] 
  [4; 500; 6; 7; 8; 289; 21; -105; -277; 104; 200; 3; 300; 5; 700; 800; -200; -901; 900; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [
        compute in H; try congruence; compute; reflexivity
        | ]).
      compute. reflexivity.
    + split.
      * simpl.
        change ([300; 7; 21; 104; 4; 900; 800]) with ([300; 7; 21; 104] ++ 4 :: [900; 800]).
        apply Permutation_cons_app. simpl.
        change ([300; 7; 21; 104; 900; 800]) with ([300] ++ 7 :: [21; 104; 900; 800]).
        apply Permutation_cons_app. simpl.
        change ([300; 21; 104; 900; 800]) with ([300] ++ 21 :: [104; 900; 800]).
        apply Permutation_cons_app. simpl.
        change ([300; 104; 900; 800]) with ([300] ++ 104 :: [900; 800]).
        apply Permutation_cons_app. simpl.
        change ([300; 900; 800]) with ([] ++ 300 :: [900; 800]).
        apply Permutation_cons_app. simpl.
        change ([900; 800]) with ([900] ++ 800 :: []).
        apply Permutation_cons_app. simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | 
          try apply HdRel_nil; 
          try (apply HdRel_cons; apply Z.leb_le; reflexivity) 
        ]).
        apply Sorted_nil.
Qed.