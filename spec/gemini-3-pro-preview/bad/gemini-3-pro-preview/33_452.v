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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; 105; -901; 800; 1000; 6; 7] 
  [-901; 500; 6; 4; 8; 289; 6; -105; -277; 7; 200; 3; 20; 5; 700; 104; -200; 105; 300; 800; 1000; 900; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-901 :: [300; 7; 20; 104; 4; 900; 6]).
        { apply Permutation_sym. apply (Permutation_middle _ [300; 7; 20; 104; 4; 900] [6] -901). }
        constructor.
        transitivity (4 :: [300; 7; 20; 104; 900; 6]).
        { apply Permutation_sym. apply (Permutation_middle _ [300; 7; 20; 104] [900; 6] 4). }
        constructor.
        transitivity (6 :: [300; 7; 20; 104; 900]).
        { apply Permutation_sym. apply (Permutation_middle _ [300; 7; 20; 104; 900] [] 6). }
        constructor.
        transitivity (7 :: [300; 20; 104; 900]).
        { apply Permutation_sym. apply (Permutation_middle _ [300] [20; 104; 900] 7). }
        constructor.
        transitivity (20 :: [300; 104; 900]).
        { apply Permutation_sym. apply (Permutation_middle _ [300] [104; 900] 20). }
        constructor.
        transitivity (104 :: [300; 900]).
        { apply Permutation_sym. apply (Permutation_middle _ [300] [900] 104). }
        constructor.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; apply Z.leb_le; reflexivity) ]).
        apply Sorted_nil.
Qed.