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
  [1; 5; 3; -5; 23; -3; 3; -9; 0; 123; -1; -10; -1] 
  [-1; 5; -1; -5; 0; -3; 1; -9; 3; 123; 3; -10; 23].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation check *)
        simpl.
        (* Goal: Permutation [1; 3; 23; 3; 0; -1; -1] [-1; -1; 0; 1; 3; 3; 23] *)
        (* Match 1 *)
        change [-1; -1; 0; 1; 3; 3; 23] with ([-1; -1; 0] ++ 1 :: [3; 3; 23]).
        apply Permutation_cons_app.
        simpl.
        (* Match 3 *)
        change [-1; -1; 0; 3; 3; 23] with ([-1; -1; 0] ++ 3 :: [3; 23]).
        apply Permutation_cons_app.
        simpl.
        (* Match 23 *)
        change [-1; -1; 0; 3; 23] with ([-1; -1; 0; 3] ++ 23 :: []).
        apply Permutation_cons_app.
        simpl.
        (* Match 3 *)
        change [-1; -1; 0; 3] with ([-1; -1; 0] ++ 3 :: []).
        apply Permutation_cons_app.
        simpl.
        (* Match 0 *)
        change [-1; -1; 0] with ([-1; -1] ++ 0 :: []).
        apply Permutation_cons_app.
        simpl.
        (* Match -1 *)
        change [-1; -1] with ([] ++ -1 :: [-1]).
        apply Permutation_cons_app.
        simpl.
        (* Match -1 *)
        apply Permutation_refl.
      * (* Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.