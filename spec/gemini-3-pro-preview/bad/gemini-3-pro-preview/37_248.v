Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec 
  [5; -13; 3; -5; 2; -10; -3; -2; 3; -8; 0; 1; -10; -9] 
  [-10; -13; -3; -5; 0; -10; 2; -2; 3; -8; 3; 1; 5; -9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in Hodd |- *; try discriminate; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (5 :: [-10; -3; 0; 2; 3; 3]).
        { constructor.
          apply Permutation_trans with (3 :: [-10; -3; 0; 2; 3]).
          { constructor.
            apply Permutation_trans with (2 :: [-10; -3; 0; 3]).
            { constructor.
              apply Permutation_trans with (-3 :: [-10; 0; 3]).
              { constructor.
                apply Permutation_trans with (3 :: [-10; 0]).
                { constructor.
                  apply Permutation_trans with (0 :: [-10]).
                  { constructor. apply Permutation_refl. }
                  { change [-10; 0] with ([-10] ++ 0 :: []). apply Permutation_middle. }
                }
                { change [-10; 0; 3] with ([-10; 0] ++ 3 :: []). apply Permutation_middle. }
              }
              { change [-10; -3; 0; 3] with ([-10] ++ -3 :: [0; 3]). apply Permutation_middle. }
            }
            { change [-10; -3; 0; 2; 3] with ([-10; -3; 0] ++ 2 :: [3]). apply Permutation_middle. }
          }
          { change [-10; -3; 0; 2; 3; 3] with ([-10; -3; 0; 2] ++ 3 :: [3]). apply Permutation_middle. }
        }
        { change [-10; -3; 0; 2; 3; 3; 5] with ([-10; -3; 0; 2; 3; 3] ++ [5]). apply Permutation_middle. }
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.