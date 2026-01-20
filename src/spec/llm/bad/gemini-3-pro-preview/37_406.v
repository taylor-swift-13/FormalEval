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
  [5; 2; -13; 3; -5; 2; -10; -3; -2; 3; 2; -8; 0; -10; -9] 
  [-13; 2; -10; 3; -9; 2; -5; -3; -2; 3; 0; -8; 2; -10; 5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Efficiently check each index by destructing i boundedly *)
      do 15 (destruct i; [ 
        simpl in Hodd; try discriminate; simpl; reflexivity 
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -13; -5; -10; -2; 2; 0; -9] [-13; -10; -9; -5; -2; 0; 2; 5] *)
        
        (* Move 5 to front *)
        apply Permutation_trans with (l' := 5 :: [-13; -10; -9; -5; -2; 0; 2]).
        { apply Permutation_sym. 
          change [-13; -10; -9; -5; -2; 0; 2; 5] with ([-13; -10; -9; -5; -2; 0; 2] ++ [5]).
          apply Permutation_middle. }
        apply Permutation_cons.
        
        (* -13 is already at head *)
        apply Permutation_cons.

        (* Move -5 to front *)
        apply Permutation_trans with (l' := -5 :: [-10; -9; -2; 0; 2]).
        { apply Permutation_sym.
          change [-10; -9; -5; -2; 0; 2] with ([-10; -9] ++ -5 :: [-2; 0; 2]).
          apply Permutation_middle. }
        apply Permutation_cons.

        (* -10 is already at head *)
        apply Permutation_cons.

        (* Move -2 to front *)
        apply Permutation_trans with (l' := -2 :: [-9; 0; 2]).
        { apply Permutation_sym.
          change [-9; -2; 0; 2] with ([-9] ++ -2 :: [0; 2]).
          apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 2 to front *)
        apply Permutation_trans with (l' := 2 :: [-9; 0]).
        { apply Permutation_sym.
          change [-9; 0; 2] with ([-9; 0] ++ 2 :: []).
          apply Permutation_middle. }
        apply Permutation_cons.

        (* Swap 0 and -9 *)
        apply Permutation_swap.

      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.