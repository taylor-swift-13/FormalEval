Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Psatz.
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
  [300; 500; 6; 7; 291; 8; -3; 289; 20; 104; -277; 8; 104; 200; -8; 700; 900; -901; 800; 1000; 290; -8]
  [-8; 500; 6; -3; 291; 8; 7; 289; 20; 104; -277; 8; 104; 200; -8; 300; 900; -901; 700; 1000; 290; 800].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i as [|i]; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -8 :: [300; 7; -3; 104; 104; 700; 800]).
        { apply perm_skip. 
          apply Permutation_trans with (l' := -3 :: [300; 7; 104; 104; 700; 800]).
          { apply perm_skip.
            apply Permutation_trans with (l' := 7 :: [300; 104; 104; 700; 800]).
            { apply perm_skip.
              apply Permutation_trans with (l' := 104 :: [300; 104; 700; 800]).
              { apply perm_skip.
                apply Permutation_trans with (l' := 104 :: [300; 700; 800]).
                { apply perm_skip. apply Permutation_refl. }
                { apply Permutation_sym. change [300; 104; 700; 800] with ([300] ++ 104 :: [700; 800]). apply Permutation_middle. }
              }
              { apply Permutation_sym. change [300; 104; 104; 700; 800] with ([300] ++ 104 :: [104; 700; 800]). apply Permutation_middle. }
            }
            { apply Permutation_sym. change [300; 7; 104; 104; 700; 800] with ([300] ++ 7 :: [104; 104; 700; 800]). apply Permutation_middle. }
          }
          { apply Permutation_sym. change [300; 7; -3; 104; 104; 700; 800] with ([300; 7] ++ -3 :: [104; 104; 700; 800]). apply Permutation_middle. }
        }
        { apply (Permutation_middle _ [300; 7; -3; 104; 104; 700; 800] []). }
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try apply HdRel_cons; try lia ]).
        apply Sorted_nil.
Qed.