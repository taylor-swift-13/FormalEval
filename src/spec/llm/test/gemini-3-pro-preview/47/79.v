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

Example test_median : median_spec [1; 3; -1; 9; 7; 8; 0; 10; 10; 8]%Z (15#2).
Proof.
  unfold median_spec.
  exists [-1; 0; 1; 3; 7; 8; 8; 9; 10; 10]%Z.
  split.
  - apply Permutation_cons_app with (l1 := [-1; 0]%Z). simpl.
    apply Permutation_cons_app with (l1 := [-1; 0]%Z). simpl.
    apply Permutation_cons_app with (l1 := []%Z). simpl.
    apply Permutation_cons_app with (l1 := [0; 7; 8; 8]%Z). simpl.
    apply Permutation_cons_app with (l1 := [0]%Z). simpl.
    apply Permutation_cons_app with (l1 := [0]%Z). simpl.
    apply Permutation_cons_app with (l1 := []%Z). simpl.
    apply Permutation_cons_app with (l1 := [8]%Z). simpl.
    apply Permutation_cons_app with (l1 := [8]%Z). simpl.
    apply Permutation_cons_app with (l1 := []%Z). simpl.
    constructor.
  - split.
    + repeat constructor; try lia.
    + split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.