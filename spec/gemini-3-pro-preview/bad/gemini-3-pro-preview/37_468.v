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
  [11; -7; -5; 2; 10; 2; 9; 5; -3; 2; 8; 3; 7] 
  [-5; -7; -3; 2; 7; 2; 8; 5; 9; 2; 10; 3; 11].
Proof.
  unfold sort_even_spec.
  split.
  { simpl. reflexivity. }
  split.
  {
    intros i Hlen Hodd.
    do 13 (destruct i as [|i]; [ simpl in *; try discriminate; try reflexivity | ]).
    simpl in Hlen. lia.
  }
  split.
  {
    simpl.
    transitivity (-5 :: [11; 10; 9; -3; 8; 7]).
    { apply Permutation_swap. }
    apply Permutation_cons.
    transitivity (-3 :: [11; 10; 9; 8; 7]).
    { change [11; 10; 9; -3; 8; 7] with ([11; 10; 9] ++ -3 :: [8; 7]).
      apply Permutation_sym, Permutation_middle. }
    apply Permutation_cons.
    transitivity (7 :: [11; 10; 9; 8]).
    { change [11; 10; 9; 8; 7] with ([11; 10; 9; 8] ++ 7 :: []).
      apply Permutation_sym, Permutation_middle. }
    apply Permutation_cons.
    transitivity (8 :: [11; 10; 9]).
    { change [11; 10; 9; 8] with ([11; 10; 9] ++ 8 :: []).
      apply Permutation_sym, Permutation_middle. }
    apply Permutation_cons.
    transitivity (9 :: [11; 10]).
    { change [11; 10; 9] with ([11; 10] ++ 9 :: []).
      apply Permutation_sym, Permutation_middle. }
    apply Permutation_cons.
    apply Permutation_swap.
  }
  {
    simpl.
    repeat (apply Sorted_cons; [
      match goal with
      | |- HdRel _ _ [] => apply HdRel_nil
      | |- HdRel _ _ (_ :: _) => apply HdRel_cons; simpl; lia
      end
    | ]).
    apply Sorted_nil.
  }
Qed.