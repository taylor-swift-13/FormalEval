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

Example test_sort_even_case : sort_even_spec [5; 3; -5; 23; -3; 3; -9; 0; 123; 1; -10] [-10; 3; -9; 23; -5; 3; -3; 0; 5; 1; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -5; -3; -9; 123; -10] [-10; -9; -5; -3; 5; 123] *)
        transitivity (5 :: [-10; -9; -5; -3; 123]).
        { apply perm_skip.
          transitivity (-5 :: [-10; -9; -3; 123]).
          { apply perm_skip.
            transitivity (-3 :: [-10; -9; 123]).
            { apply perm_skip.
              transitivity (-9 :: [-10; 123]).
              { apply perm_skip.
                apply perm_swap. }
              { change [-10; -9; 123] with ([-10] ++ -9 :: [123]).
                apply Permutation_sym. apply Permutation_middle. }
            }
            { change [-10; -9; -3; 123] with ([-10; -9] ++ -3 :: [123]).
              apply Permutation_sym. apply Permutation_middle. }
          }
          { change [-10; -9; -5; -3; 123] with ([-10; -9] ++ -5 :: [-3; 123]).
            apply Permutation_sym. apply Permutation_middle. }
        }
        { change [-10; -9; -5; -3; 5; 123] with ([-10; -9; -5; -3] ++ 5 :: [123]).
          apply Permutation_sym. apply Permutation_middle. }
      * (* 4. Sorted check *)
        simpl.
        repeat constructor; simpl; try lia.
Qed.