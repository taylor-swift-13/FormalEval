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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 7; 3; 4; 5; 700; 900; -200; -901; 800; 1000]
  [-901; 500; 6; 3; 8; 289; 7; -105; -277; 20; 200; 7; 104; 4; 5; 300; 900; -200; 700; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* Check the first 21 indices explicitly *)
      do 21 (destruct i; [ simpl; try (intros C; exfalso; apply C; reflexivity); reflexivity | ]).
      (* For i >= 21, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        vm_compute.
        (* Goal: Permutation [-901; 3; 7; 20; 104; 300; 700] [300; 7; 20; 104; 3; 700; -901] *)
        apply Permutation_sym.
        (* Sort the right hand list step by step to match the left hand list *)
        transitivity (-901 :: [300; 7; 20; 104; 3; 700]).
        { change [300; 7; 20; 104; 3; 700; -901] with ([300; 7; 20; 104; 3; 700] ++ -901 :: []).
          apply Permutation_middle. }
        constructor.
        transitivity (3 :: [300; 7; 20; 104; 700]).
        { change [300; 7; 20; 104; 3; 700] with ([300; 7; 20; 104] ++ 3 :: [700]).
          apply Permutation_middle. }
        constructor.
        transitivity (7 :: [300; 20; 104; 700]).
        { change [300; 7; 20; 104; 700] with ([300] ++ 7 :: [20; 104; 700]).
          apply Permutation_middle. }
        constructor.
        transitivity (20 :: [300; 104; 700]).
        { change [300; 20; 104; 700] with ([300] ++ 20 :: [104; 700]).
          apply Permutation_middle. }
        constructor.
        transitivity (104 :: [300; 700]).
        { change [300; 104; 700] with ([300] ++ 104 :: [700]).
          apply Permutation_middle. }
        constructor.
        apply Permutation_refl.
      * (* Sorted *)
        vm_compute.
        repeat match goal with
        | |- Sorted ?R [] => apply Sorted_nil
        | |- Sorted ?R (_ :: _) => apply Sorted_cons
        | |- HdRel ?R ?a [] => apply HdRel_nil
        | |- HdRel ?R ?a (?b :: _) => apply HdRel_cons; simpl; try lia
        end.
Qed.