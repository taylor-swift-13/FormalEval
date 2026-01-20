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
  [5; -6; 2; -7; -3; 3; -9; 0; 1; -10; 10; 2; 1] 
  [-9; -6; -3; -7; 1; 3; 1; 0; 2; -10; 5; 2; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ 
        simpl in Hodd; try discriminate; simpl; reflexivity 
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; 2; -3; -9; 1; 10; 1] [-9; -3; 1; 1; 2; 5; 10] *)
        apply Permutation_sym.
        (* Goal: Permutation [-9; -3; 1; 1; 2; 5; 10] [5; 2; -3; -9; 1; 10; 1] *)
        
        (* 1. Pull -9 *)
        transitivity (-9 :: [5; 2; -3; 1; 10; 1]).
        2: { change [5; 2; -3; -9; 1; 10; 1] with ([5; 2; -3] ++ -9 :: [1; 10; 1]). apply Permutation_middle. }
        apply perm_skip.
        
        (* 2. Pull -3 *)
        transitivity (-3 :: [5; 2; 1; 10; 1]).
        2: { change [5; 2; -3; 1; 10; 1] with ([5; 2] ++ -3 :: [1; 10; 1]). apply Permutation_middle. }
        apply perm_skip.

        (* 3. Pull 1 *)
        transitivity (1 :: [5; 2; 10; 1]).
        2: { change [5; 2; 1; 10; 1] with ([5; 2] ++ 1 :: [10; 1]). apply Permutation_middle. }
        apply perm_skip.

        (* 4. Pull 1 *)
        transitivity (1 :: [5; 2; 10]).
        2: { change [5; 2; 10; 1] with ([5; 2; 10] ++ 1 :: []). apply Permutation_middle. }
        apply perm_skip.

        (* 5. Pull 2 *)
        transitivity (2 :: [5; 10]).
        2: { change [5; 2; 10] with ([5] ++ 2 :: [10]). apply Permutation_middle. }
        apply perm_skip.

        (* 6. Pull 5 *)
        transitivity (5 :: [10]).
        2: { change [5; 10] with ([] ++ 5 :: [10]). apply Permutation_middle. }
        apply perm_skip.
        
        (* 7. Last element *)
        apply Permutation_refl.

      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try (apply HdRel_cons; lia)]).
        apply Sorted_nil.
Qed.