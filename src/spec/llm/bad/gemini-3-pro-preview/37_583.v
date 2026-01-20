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
  [8; -5; -7; -2; 10; 11; 0; 8; 9; 5; 2; 8; 4; 7; 0] 
  [-7; -5; 0; -2; 0; 11; 2; 8; 4; 5; 8; 8; 9; 7; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [8; -7; 10; 0; 9; 2; 4; 0] *)
        (* Target: [-7; 0; 0; 2; 4; 8; 9; 10] *)
        
        (* Move -7 to front *)
        transitivity (-7 :: [8; 10; 0; 9; 2; 4; 0]).
        { apply Permutation_swap. }
        apply Permutation_cons.
        
        (* Move 0 to front (from index 2) *)
        transitivity (0 :: [8; 10; 9; 2; 4; 0]).
        { symmetry. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 0 to front (from end) *)
        transitivity (0 :: [8; 10; 9; 2; 4]).
        { symmetry. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 2 to front (from index 3) *)
        transitivity (2 :: [8; 10; 9; 4]).
        { symmetry. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 4 to front (from end) *)
        transitivity (4 :: [8; 10; 9]).
        { symmetry. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* 8 matches *)
        apply Permutation_cons.
        
        (* Swap 10 and 9 *)
        apply Permutation_swap.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; simpl; lia | ]).
        apply Sorted_nil.
Qed.