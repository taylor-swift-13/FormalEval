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
Example test_median : median_spec [13; 0; 0; 1; 1; 0]%Z (1#2).
Proof.
  unfold median_spec.
  exists [0; 0; 0; 1; 1; 13]%Z.
  split.
  - transitivity (13 :: [0; 0; 0; 1; 1])%Z.
    + apply Permutation_sym.
      apply Permutation_cons_app with (l1 := [0; 0; 0; 1; 1]%Z) (l2 := []%Z).
      simpl. reflexivity.
    + constructor.
      constructor.
      constructor.
      apply Permutation_cons_app with (l1 := [1; 1]%Z) (l2 := []%Z).
      simpl. reflexivity.
  - split.
    + repeat constructor; simpl; try lia.
    + simpl.
      split.
      * lia.
      * split.
        -- lia.
        -- simpl. reflexivity.
Qed.