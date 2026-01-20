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
  [5; -2; -11; 4; 23; 6; 3; 11; 12; -10; 4] 
  [-11; -2; 3; 4; 4; 6; 5; 11; 12; -10; 23].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Move -11 *)
        change [5; -11; 23; 3; 12; 4] with ([5] ++ -11 :: [23; 3; 12; 4]).
        transitivity (-11 :: [5] ++ [23; 3; 12; 4]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        (* Move 3 *)
        change [5; 23; 3; 12; 4] with ([5; 23] ++ 3 :: [12; 4]).
        transitivity (3 :: [5; 23] ++ [12; 4]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        (* Move 4 *)
        change [5; 23; 12; 4] with ([5; 23; 12] ++ 4 :: []).
        transitivity (4 :: [5; 23; 12] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        (* 5 matches *)
        apply Permutation_cons.
        (* Move 12 *)
        change [23; 12] with ([23] ++ 12 :: []).
        transitivity (12 :: [23] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.