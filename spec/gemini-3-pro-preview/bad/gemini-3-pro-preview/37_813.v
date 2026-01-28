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
  [5; 3; -5; 23; -3; 3; -9; 0; 123; 1; 3; -10; 5] 
  [-9; 3; -5; 23; -3; 3; 3; 0; 5; 1; 5; -10; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := 5 :: ([-9; -5; -3; 3] ++ [5; 123])).
        { apply Permutation_cons.
          apply Permutation_trans with (l' := -5 :: ([-9] ++ [-3; 3; 5; 123])).
          { apply Permutation_cons.
            apply Permutation_trans with (l' := -3 :: ([-9] ++ [3; 5; 123])).
            { apply Permutation_cons.
              apply Permutation_cons. (* -9 matches head *)
              apply Permutation_trans with (l' := 123 :: ([3; 5] ++ [])).
              { apply Permutation_cons.
                apply Permutation_cons. (* 3 matches head *)
                apply Permutation_cons. (* 5 matches head *)
                apply Permutation_nil.
              }
              change [3; 5; 123] with ([3; 5] ++ 123 :: []).
              apply Permutation_sym. apply Permutation_middle.
            }
            change [-9; -3; 3; 5; 123] with ([-9] ++ -3 :: [3; 5; 123]).
            apply Permutation_sym. apply Permutation_middle.
          }
          change [-9; -5; -3; 3; 5; 123] with ([-9] ++ -5 :: [-3; 3; 5; 123]).
          apply Permutation_sym. apply Permutation_middle.
        }
        change [-9; -5; -3; 3; 5; 5; 123] with ([-9; -5; -3; 3] ++ 5 :: [5; 123]).
        apply Permutation_sym. apply Permutation_middle.
      * simpl.
        repeat (constructor; try lia).
Qed.