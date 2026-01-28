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
Example test_median : median_spec [10; 4; 30; 40; 51]%Z (30#1).
Proof.
  unfold median_spec.
  exists [4; 10; 30; 40; 51]%Z.
  split.
  - apply Permutation_sym.
    apply Permutation_cons_app with (l1 := [4]%Z) (l2 := [30; 40; 51]%Z).
    simpl. reflexivity.
  - split.
    + repeat constructor; simpl; try lia.
    + simpl.
      split.
      * lia.
      * simpl. reflexivity.
Qed.