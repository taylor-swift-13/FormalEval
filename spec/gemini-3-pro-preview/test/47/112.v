Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition median_spec (l : list R) (res : R) : Prop :=
  exists sorted_l,
    Permutation l sorted_l /\
    Sorted Rle sorted_l /\
    let n := length l in
    (n > 0)%nat /\
    if Nat.odd n then
      res = nth (n / 2) sorted_l 0
    else
      res = (nth (n / 2 - 1) sorted_l 0 + nth (n / 2) sorted_l 0) / 2.

Example test_median : median_spec [3.5; 5.7; 6.1; 7.2; 10.0; 12.5; 13.0; 14.5; 16.8; 19.7]%R 11.25%R.
Proof.
  unfold median_spec.
  exists [3.5; 5.7; 6.1; 7.2; 10.0; 12.5; 13.0; 14.5; 16.8; 19.7]%R.
  split.
  - (* Prove Permutation *)
    apply Permutation_refl.
  - split.
    + (* Prove Sorted *)
      repeat constructor; try lra.
    + (* Prove Result *)
      split.
      * simpl. lia.
      * simpl. lra.
Qed.