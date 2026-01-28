Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.

Import ListNotations.

Open Scope Z_scope.
Open Scope Q_scope.

(* Specification definition *)
Definition median_spec (l : list Z) (m : Q) : Prop :=
  exists sl,
    Permutation sl l /\
    Sorted Z.le sl /\
    let n := length sl in
    let mid := Nat.div n 2 in
    (if Nat.odd n
     then Nat.lt mid n /\ m = inject_Z (nth mid sl 0%Z)
     else Nat.le 2 n /\ Nat.lt mid n /\
          m = (inject_Z (nth (Nat.pred mid) sl 0%Z) + inject_Z (nth mid sl 0%Z)) / (2#1)).

(* Test case *)
Example test_median : median_spec [7; 10; 3; 3; 3; 5; 3; 3; 3]%Z (3#1).
Proof.
  unfold median_spec.
  exists [3; 3; 3; 3; 3; 3; 5; 7; 10]%Z.
  split.
  - (* Permutation *)
    (* We prove Permutation [3; 3; 3; 3; 3; 3; 5; 7; 10] [7; 10; 3; 3; 3; 5; 3; 3; 3] by successively moving the head of LHS to its position in RHS *)
    apply Permutation_cons_app with (l1 := [7; 10]%Z) (l2 := [3; 3; 5; 3; 3; 3]%Z). simpl.
    apply Permutation_cons_app with (l1 := [7; 10]%Z) (l2 := [3; 5; 3; 3; 3]%Z). simpl.
    apply Permutation_cons_app with (l1 := [7; 10]%Z) (l2 := [5; 3; 3; 3]%Z). simpl.
    apply Permutation_cons_app with (l1 := [7; 10; 5]%Z) (l2 := [3; 3]%Z). simpl.
    apply Permutation_cons_app with (l1 := [7; 10; 5]%Z) (l2 := [3]%Z). simpl.
    apply Permutation_cons_app with (l1 := [7; 10; 5]%Z) (l2 := []%Z). simpl.
    apply Permutation_cons_app with (l1 := [7; 10]%Z) (l2 := []%Z). simpl.
    apply Permutation_cons_app with (l1 := []%Z) (l2 := [10]%Z). simpl.
    apply Permutation_cons_app with (l1 := []%Z) (l2 := []%Z). simpl.
    reflexivity.
  - split.
    + (* Sorted *)
      repeat constructor; simpl; try lia.
    + (* Result *)
      simpl.
      split.
      * lia.
      * reflexivity.
Qed.