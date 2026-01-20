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
  [2; 1; 1; 2; 2; 4; 5; 6; 7; 10; -8; 1] 
  [-8; 1; 1; 2; 2; 4; 2; 6; 5; 10; 7; 1].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Handle indices 0 to 11 explicitly *)
      do 12 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      (* Handle indices >= 12 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Use Permutation_cons_app to match elements one by one *)
        apply Permutation_cons_app with (l1 := [-8; 1]) (l2 := [2; 5; 7]). simpl.
        apply Permutation_cons_app with (l1 := [-8]) (l2 := [2; 5; 7]). simpl.
        apply Permutation_cons_app with (l1 := [-8]) (l2 := [5; 7]). simpl.
        apply Permutation_cons_app with (l1 := [-8]) (l2 := [7]). simpl.
        apply Permutation_cons_app with (l1 := [-8]) (l2 := []). simpl.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| first [ apply HdRel_cons; simpl; lia | apply HdRel_nil ] ]).
        apply Sorted_nil.
Qed.