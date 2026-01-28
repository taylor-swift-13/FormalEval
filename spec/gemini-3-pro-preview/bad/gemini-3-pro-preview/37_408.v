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
  [5; 3; -5; -4; 2; -3; 3; 0; 123; 1; -10; -2; 123] 
  [-10; 3; -5; -4; 2; -3; 3; 0; 5; 1; 123; -2; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [5; -5; 2; 3; 123; -10; 123] *)
        (* RHS: [-10; -5; 2; 3; 5; 123; 123] *)
        change [-10; -5; 2; 3; 5; 123; 123] with ([-10; -5; 2; 3] ++ 5 :: [123; 123]).
        apply Permutation_trans with (5 :: [-10; -5; 2; 3] ++ [123; 123]).
        { apply Permutation_cons. simpl.
          change [-10; -5; 2; 3; 123; 123] with ([-10] ++ -5 :: [2; 3; 123; 123]).
          apply Permutation_trans with (-5 :: [-10] ++ [2; 3; 123; 123]).
          { apply Permutation_cons. simpl.
            change [-10; 2; 3; 123; 123] with ([-10] ++ 2 :: [3; 123; 123]).
            apply Permutation_trans with (2 :: [-10] ++ [3; 123; 123]).
            { apply Permutation_cons. simpl.
              change [-10; 3; 123; 123] with ([-10] ++ 3 :: [123; 123]).
              apply Permutation_trans with (3 :: [-10] ++ [123; 123]).
              { apply Permutation_cons. simpl.
                change [-10; 123; 123] with ([-10] ++ 123 :: [123]).
                apply Permutation_trans with (123 :: [-10] ++ [123]).
                { apply Permutation_cons. simpl.
                  apply Permutation_refl. }
                apply Permutation_middle. }
              apply Permutation_middle. }
            apply Permutation_middle. }
          apply Permutation_middle. }
        apply Permutation_middle.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; [ | simpl; lia ]).
        apply Sorted_nil.
Qed.