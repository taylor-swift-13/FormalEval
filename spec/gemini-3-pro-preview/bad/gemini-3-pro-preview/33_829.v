Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [300; 500; 6; 7; 9; 8; 289; 20; -105; -277; 700; 103; 200; 7; 3; 4; 5; 700; 900; -200; -901; 800; 1000] 
  [-277; 500; 6; 4; 9; 8; 7; 20; -105; 200; 700; 103; 289; 7; 3; 300; 5; 700; 800; -200; -901; 900; 1000].
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
        apply Permutation_trans with (-277 :: [300; 7; 289] ++ [200; 4; 900; 800]).
        { apply Permutation_cons.
          apply Permutation_trans with (4 :: [300; 7; 289; 200] ++ [900; 800]).
          { apply Permutation_cons.
            apply Permutation_trans with (7 :: [300] ++ [289; 200; 900; 800]).
            { apply Permutation_cons.
              apply Permutation_trans with (200 :: [300; 289] ++ [900; 800]).
              { apply Permutation_cons.
                apply Permutation_trans with (289 :: [300] ++ [900; 800]).
                { apply Permutation_cons.
                  apply Permutation_cons.
                  apply Permutation_swap. }
                { change [300; 289; 900; 800] with ([300] ++ 289 :: [900; 800]). apply Permutation_middle. }
              }
              { change [300; 289; 200; 900; 800] with ([300; 289] ++ 200 :: [900; 800]). apply Permutation_middle. }
            }
            { change [300; 7; 289; 200; 900; 800] with ([300] ++ 7 :: [289; 200; 900; 800]). apply Permutation_middle. }
          }
          { change [300; 7; 289; 200; 4; 900; 800] with ([300; 7; 289; 200] ++ 4 :: [900; 800]). apply Permutation_middle. }
        }
        { change [300; 7; 289; -277; 200; 4; 900; 800] with ([300; 7; 289] ++ -277 :: [200; 4; 900; 800]). apply Permutation_middle. }
      * simpl.
        repeat (constructor; [ simpl; try lia | ]).
Qed.