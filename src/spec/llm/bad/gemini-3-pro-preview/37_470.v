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
  [5; 3; 6; -5; 2; -3; -9; 0; 123; 1; -10; 3; 123; 123; -9] 
  [-10; 3; -9; -5; -9; -3; 2; 0; 5; 1; 6; 3; 123; 123; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ try (simpl in Hodd; discriminate); simpl; reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        transitivity (5 :: [-10; -9; -9; 2; 6; 123; 123]).
        2: { symmetry. change ([-10; -9; -9; 2; 5; 6; 123; 123]) with ([-10; -9; -9; 2] ++ 5 :: [6; 123; 123]). apply Permutation_middle. }
        constructor.
        transitivity (6 :: [-10; -9; -9; 2; 123; 123]).
        2: { symmetry. change ([-10; -9; -9; 2; 6; 123; 123]) with ([-10; -9; -9; 2] ++ 6 :: [123; 123]). apply Permutation_middle. }
        constructor.
        transitivity (2 :: [-10; -9; -9; 123; 123]).
        2: { symmetry. change ([-10; -9; -9; 2; 123; 123]) with ([-10; -9; -9] ++ 2 :: [123; 123]). apply Permutation_middle. }
        constructor.
        transitivity (-9 :: [-10; -9; 123; 123]).
        2: { symmetry. change ([-10; -9; -9; 123; 123]) with ([-10] ++ -9 :: [-9; 123; 123]). apply Permutation_middle. }
        constructor.
        transitivity (123 :: [-10; -9; 123]).
        2: { symmetry. change ([-10; -9; 123; 123]) with ([-10; -9] ++ 123 :: [123]). apply Permutation_middle. }
        constructor.
        transitivity (-10 :: [-9; 123]).
        2: { symmetry. change ([-10; -9; 123]) with ([] ++ -10 :: [-9; 123]). apply Permutation_middle. }
        constructor.
        transitivity (123 :: [-9]).
        2: { symmetry. change ([-9; 123]) with ([-9] ++ 123 :: []). apply Permutation_middle. }
        constructor.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.