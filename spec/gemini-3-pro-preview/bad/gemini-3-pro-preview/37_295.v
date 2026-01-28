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
  [5; 3; -4; 2; 3; -9; 0; 123; 1; -10; 2; -3; -10] 
  [-10; 3; -4; 2; 0; -9; 1; 123; 2; -10; 3; -3; 5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ 
        simpl in Hodd; try discriminate Hodd; simpl; try reflexivity 
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply Permutation_cons_app with (l1 := [-10; -4; 0; 1; 2; 3]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := [-10]) (l2 := [0; 1; 2; 3]). simpl.
        apply Permutation_cons_app with (l1 := [-10; 0; 1; 2]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := [-10]) (l2 := [1; 2]). simpl.
        apply Permutation_cons_app with (l1 := [-10]) (l2 := [2]). simpl.
        apply Permutation_cons_app with (l1 := [-10]) (l2 := []). simpl.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| first [apply HdRel_cons; lia | apply HdRel_nil] ]).
        apply Sorted_nil.
Qed.