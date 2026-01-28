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
  [5; 3; 10; -5; 2; -12; -3; 3; -9; 1; 123; 1; -10; 10; -5] 
  [-10; 3; -9; -5; -5; -12; -3; 3; 2; 1; 5; 1; 10; 10; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Odd indices *)
      intros i Hlen Hodd.
      (* We check each index explicitly to avoid complex automation on large terms *)
      do 15 (destruct i as [|i]; [ simpl in *; try discriminate; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation *)
        simpl.
        (* We use transitivity and Permutation_middle to reorder the list step by step *)
        (* Target: [5; 10; 2; -3; -9; 123; -10; -5] *)
        
        (* Move 5 *)
        transitivity (5 :: [-10; -9; -5; -3; 2; 10; 123]).
        2: { change [-10; -9; -5; -3; 2; 5; 10; 123] with ([-10; -9; -5; -3; 2] ++ 5 :: [10; 123]). apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 10 *)
        transitivity (10 :: [-10; -9; -5; -3; 2; 123]).
        2: { change [-10; -9; -5; -3; 2; 10; 123] with ([-10; -9; -5; -3; 2] ++ 10 :: [123]). apply Permutation_middle. }
        apply Permutation_cons.

        (* Move 2 *)
        transitivity (2 :: [-10; -9; -5; -3; 123]).
        2: { change [-10; -9; -5; -3; 2; 123] with ([-10; -9; -5; -3] ++ 2 :: [123]). apply Permutation_middle. }
        apply Permutation_cons.

        (* Move -3 *)
        transitivity (-3 :: [-10; -9; -5; 123]).
        2: { change [-10; -9; -5; -3; 123] with ([-10; -9; -5] ++ -3 :: [123]). apply Permutation_middle. }
        apply Permutation_cons.

        (* Move -9 *)
        transitivity (-9 :: [-10; -5; 123]).
        2: { change [-10; -9; -5; 123] with ([-10] ++ -9 :: [-5; 123]). apply Permutation_middle. }
        apply Permutation_cons.

        (* Move 123 *)
        transitivity (123 :: [-10; -5]).
        2: { change [-10; -5; 123] with ([-10; -5] ++ 123 :: []). apply Permutation_middle. }
        apply Permutation_cons.

        (* Remaining: [-10; -5] matches *)
        apply Permutation_refl.

      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.