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
Example test_median : median_spec [7; 9; 3; 5]%Z (12#2).
Proof.
  unfold median_spec.
  exists [3; 5; 7; 9]%Z.
  split.
  - apply Permutation_sym.
    replace [7; 9; 3; 5]%Z with ([7; 9]%Z ++ [3; 5]%Z) by reflexivity.
    replace [3; 5; 7; 9]%Z with ([3; 5]%Z ++ [7; 9]%Z) by reflexivity.
    apply Permutation_app_comm.
  - split.
    + repeat constructor; simpl; try lia.
    + simpl.
      split.
      * lia.
      * split.
        -- lia.
        -- reflexivity.
Qed.