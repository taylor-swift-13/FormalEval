Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Micromega.Lia.
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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 0; 5; 700; 900; 18; -8; -901; 800; 1000; 0; -277; -8] 
  [-901; 500; 6; 0; 8; 289; 0; -105; -277; 7; 200; 3; 20; 5; 700; 104; 18; -8; 300; 800; 1000; 900; -277; -8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 25 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        transitivity (-901 :: [300; 7; 20; 104; 0; 900; 0]).
        { apply Permutation_sym.
          change ([300; 7; 20; 104; 0; 900; -901; 0]) with ([300; 7; 20; 104; 0; 900] ++ -901 :: [0]).
          change (-901 :: [300; 7; 20; 104; 0; 900; 0]) with (-901 :: [300; 7; 20; 104; 0; 900] ++ [0]).
          apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (0 :: [300; 7; 20; 104; 900; 0]).
        { apply Permutation_sym.
          change ([300; 7; 20; 104; 0; 900; 0]) with ([300; 7; 20; 104] ++ 0 :: [900; 0]).
          change (0 :: [300; 7; 20; 104; 900; 0]) with (0 :: [300; 7; 20; 104] ++ [900; 0]).
          apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (0 :: [300; 7; 20; 104; 900]).
        { apply Permutation_sym.
          change ([300; 7; 20; 104; 900; 0]) with ([300; 7; 20; 104; 900] ++ 0 :: []).
          change (0 :: [300; 7; 20; 104; 900]) with (0 :: [300; 7; 20; 104; 900] ++ []).
          apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (7 :: [300; 20; 104; 900]).
        { apply Permutation_sym.
          change ([300; 7; 20; 104; 900]) with ([300] ++ 7 :: [20; 104; 900]).
          change (7 :: [300; 20; 104; 900]) with (7 :: [300] ++ [20; 104; 900]).
          apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (20 :: [300; 104; 900]).
        { apply Permutation_sym.
          change ([300; 20; 104; 900]) with ([300] ++ 20 :: [104; 900]).
          change (20 :: [300; 104; 900]) with (20 :: [300] ++ [104; 900]).
          apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (104 :: [300; 900]).
        { apply Permutation_sym.
          change ([300; 104; 900]) with ([300] ++ 104 :: [900]).
          change (104 :: [300; 900]) with (104 :: [300] ++ [900]).
          apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; try lia).
Qed.