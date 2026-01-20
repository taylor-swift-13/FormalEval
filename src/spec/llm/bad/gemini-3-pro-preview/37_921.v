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
  [5; 3; 10; -5; 2; -3; 3; -9; 0; 123; 1; -10; 10; -5; 5] 
  [0; 3; 1; -5; 2; -3; 3; -9; 5; 123; 5; -10; 10; -5; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Current: [5; 10; 2; 3; 0; 1; 10; 5] *)
        (* Target:  [0; 1; 2; 3; 5; 5; 10; 10] *)
        
        (* Move 0 to front *)
        apply Permutation_trans with (0 :: [5; 10; 2; 3] ++ [1; 10; 5]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Current: [5; 10; 2; 3; 1; 10; 5] *)
        (* Target Tail: [1; 2; 3; 5; 5; 10; 10] *)
        (* Move 1 to front *)
        apply Permutation_trans with (1 :: [5; 10; 2; 3] ++ [10; 5]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        (* Current: [5; 10; 2; 3; 10; 5] *)
        (* Target Tail: [2; 3; 5; 5; 10; 10] *)
        (* Move 2 to front *)
        apply Permutation_trans with (2 :: [5; 10] ++ [3; 10; 5]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        (* Current: [5; 10; 3; 10; 5] *)
        (* Target Tail: [3; 5; 5; 10; 10] *)
        (* Move 3 to front *)
        apply Permutation_trans with (3 :: [5; 10] ++ [10; 5]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        (* Current: [5; 10; 10; 5] *)
        (* Target Tail: [5; 5; 10; 10] *)
        (* 5 is at head *)
        apply Permutation_cons.

        (* Current: [10; 10; 5] *)
        (* Target Tail: [5; 10; 10] *)
        (* Move 5 to front *)
        apply Permutation_trans with (5 :: [10; 10] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        (* Current: [10; 10] *)
        (* Target Tail: [10; 10] *)
        apply Permutation_refl.

      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.