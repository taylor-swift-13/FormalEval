Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope Q_scope.

Definition median_spec (l : list Q) (res : Q) : Prop :=
  exists sorted_l,
    Permutation l sorted_l /\
    Sorted Qle sorted_l /\
    let n := length l in
    (n > 0)%nat /\
    if Nat.odd n then
      res == nth (n / 2) sorted_l (0#1)
    else
      res == Qdiv (Qplus (nth (n / 2 - 1) sorted_l (0#1)) 
                        (nth (n / 2) sorted_l (0#1))) 
                 (2#1).

Example test_median : median_spec [27#10; 38#10; 7#1; 13#1; 74#1; 1083#10] (10#1).
Proof.
  unfold median_spec.
  exists [27#10; 38#10; 7#1; 13#1; 74#1; 1083#10].
  split.
  - reflexivity.
  - split.
    + repeat constructor; unfold Qle; simpl; lia.
    + split.
      * simpl. lia.
      * simpl. unfold Qeq. simpl. lia.
Qed.