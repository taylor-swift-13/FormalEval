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

Example test_sort_even_case : sort_even_spec [6; 3; 23; 3; -12; 3; 3; 3] [-12; 3; 3; 3; 6; 3; 23; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      do 9 (destruct i as [|i]; [ 
        simpl in Hodd; try discriminate; simpl; reflexivity 
      | simpl in Hlen; try lia ]).
    + split.
      * (* Permutation check *)
        simpl.
        (* Goal: Permutation [6; 23; -12; 3] [-12; 3; 6; 23] *)
        assert (H1: Permutation [6; 23; -12; 3] (-12 :: [6; 23; 3])).
        { change [6; 23; -12; 3] with ([6; 23] ++ -12 :: [3]). 
          apply Permutation_middle. }
        rewrite H1. apply perm_skip.
        assert (H2: Permutation [6; 23; 3] (3 :: [6; 23])).
        { change [6; 23; 3] with ([6; 23] ++ 3 :: []). 
          apply Permutation_middle. }
        rewrite H2. apply perm_skip.
        apply Permutation_refl.
      * (* Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.