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

Example test_sort_even_case : 
  sort_even_spec 
    [5%Z; 3%Z; -5%Z; 2%Z; -3%Z; -2%Z; 3%Z; -9%Z; 0%Z; 123%Z; 1%Z; -10%Z; -9%Z; -10%Z; 123%Z] 
    [-9%Z; 3%Z; -5%Z; 2%Z; -3%Z; -2%Z; 0%Z; -9%Z; 1%Z; 123%Z; 3%Z; -10%Z; 5%Z; -10%Z; 123%Z].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        change [5; -5; -3; 3; 0; 1; -9; 123] with ([5; -5; -3; 3; 0; 1] ++ -9 :: [123]).
        apply Permutation_trans with (l' := -9 :: ([5; -5; -3; 3; 0; 1] ++ [123])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        change [5; -5; -3; 3; 0; 1; 123] with ([5] ++ -5 :: [-3; 3; 0; 1; 123]).
        apply Permutation_trans with (l' := -5 :: ([5] ++ [-3; 3; 0; 1; 123])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        change [5; -3; 3; 0; 1; 123] with ([5] ++ -3 :: [3; 0; 1; 123]).
        apply Permutation_trans with (l' := -3 :: ([5] ++ [3; 0; 1; 123])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        change [5; 3; 0; 1; 123] with ([5; 3] ++ 0 :: [1; 123]).
        apply Permutation_trans with (l' := 0 :: ([5; 3] ++ [1; 123])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        change [5; 3; 1; 123] with ([5; 3] ++ 1 :: [123]).
        apply Permutation_trans with (l' := 1 :: ([5; 3] ++ [123])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        change [5; 3; 123] with ([5] ++ 3 :: [123]).
        apply Permutation_trans with (l' := 3 :: ([5] ++ [123])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.