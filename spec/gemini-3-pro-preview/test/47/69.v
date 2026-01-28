Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope Q_scope.

Definition median_spec (l : list Z) (res : Q) : Prop :=
  exists sorted_l,
    Permutation l sorted_l /\
    Sorted Z.le sorted_l /\
    let n := length l in
    (n > 0)%nat /\
    if Nat.odd n then
      res = inject_Z (nth (n / 2) sorted_l 0%Z)
    else
      res = Qdiv (Qplus (inject_Z (nth (n / 2 - 1) sorted_l 0%Z)) 
                        (inject_Z (nth (n / 2) sorted_l 0%Z))) 
                 (2#1).

Example test_median : median_spec [6; 1; 3; -1; 7; 8; 8; 10; 10; 8; 8]%Z (inject_Z 8).
Proof.
  unfold median_spec.
  exists [-1; 1; 3; 6; 7; 8; 8; 8; 8; 10; 10]%Z.
  split.
  - apply Permutation_cons_app with (l1 := [-1; 1; 3]%Z) (l2 := [7; 8; 8; 8; 8; 10; 10]%Z); simpl.
    apply Permutation_cons_app with (l1 := [-1]%Z) (l2 := [3; 7; 8; 8; 8; 8; 10; 10]%Z); simpl.
    apply Permutation_cons_app with (l1 := [-1]%Z) (l2 := [7; 8; 8; 8; 8; 10; 10]%Z); simpl.
    apply Permutation_cons_app with (l1 := []%Z) (l2 := [7; 8; 8; 8; 8; 10; 10]%Z); simpl.
    apply Permutation_cons_app with (l1 := []%Z) (l2 := [8; 8; 8; 8; 10; 10]%Z); simpl.
    apply Permutation_cons_app with (l1 := []%Z) (l2 := [8; 8; 8; 10; 10]%Z); simpl.
    apply Permutation_cons_app with (l1 := []%Z) (l2 := [8; 8; 10; 10]%Z); simpl.
    apply Permutation_cons_app with (l1 := [8; 8]%Z) (l2 := [10]%Z); simpl.
    apply Permutation_cons_app with (l1 := [8; 8]%Z) (l2 := []%Z); simpl.
    apply perm_skip.
    apply perm_skip.
    apply perm_nil.
  - split.
    + repeat constructor; try lia.
    + split.
      * simpl; lia.
      * simpl; reflexivity.
Qed.