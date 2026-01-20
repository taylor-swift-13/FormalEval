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
  [-5; -7; 2; 10; 0; 9; 5; -3; 2; 8; 3; 7; 2; 8; 3] 
  [-5; -7; 0; 10; 2; 9; 2; -3; 2; 8; 3; 7; 3; 8; 5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl; simpl in Hodd; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl get_evens.
        (* Target: [-5; 0; 2; 2; 2; 3; 3; 5] *)
        (* Current: [-5; 2; 0; 5; 2; 3; 2; 3] *)
        apply Permutation_cons.
        (* Current: [2; 0; 5; 2; 3; 2; 3] *)
        (* Move 0 to front *)
        transitivity (0 :: [2] ++ [5; 2; 3; 2; 3]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* Current: [2; 5; 2; 3; 2; 3] *)
        (* 2 matches *)
        apply Permutation_cons.
        (* Current: [5; 2; 3; 2; 3] *)
        (* Move 2 to front *)
        transitivity (2 :: [5] ++ [3; 2; 3]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* Current: [5; 3; 2; 3] *)
        (* Move 2 to front *)
        transitivity (2 :: [5; 3] ++ [3]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* Current: [5; 3; 3] *)
        (* Move 3 to front *)
        transitivity (3 :: [5] ++ [3]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* Current: [5; 3] *)
        (* Move 3 to front *)
        transitivity (3 :: [5] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* Current: [5] *)
        apply Permutation_cons.
        apply Permutation_nil.
      * (* 4. Sorted check *)
        simpl get_evens.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia || apply HdRel_nil ]).
        apply Sorted_nil.
Qed.