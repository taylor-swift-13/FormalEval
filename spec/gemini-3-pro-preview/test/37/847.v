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

Example test_sort_even_case : sort_even_spec [5; 10; -6; 2; 3; -9; 0; 1; -10; 10; 2] [-10; 10; -6; 2; 0; -9; 2; 1; 3; 10; 5].
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
        (* LHS: [5; -6; 3; 0; -10; 2] *)
        (* RHS: [-10; -6; 0; 2; 3; 5] *)
        apply Permutation_cons_app with (l1 := [-10; -6; 0; 2; 3]) (l2 := []).
        simpl.
        apply Permutation_cons_app with (l1 := [-10]) (l2 := [0; 2; 3]).
        simpl.
        apply Permutation_cons_app with (l1 := [-10; 0; 2]) (l2 := []).
        simpl.
        apply Permutation_cons_app with (l1 := [-10]) (l2 := [2]).
        simpl.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.