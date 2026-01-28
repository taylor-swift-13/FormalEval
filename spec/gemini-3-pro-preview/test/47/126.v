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

Example test_median : median_spec [2; 5; 6; 8; 10; 12; 14; 19; 22; 8; 2]%Z (inject_Z 8).
Proof.
  unfold median_spec.
  exists [2; 2; 5; 6; 8; 8; 10; 12; 14; 19; 22]%Z.
  split.
  - apply perm_skip.
    apply Permutation_trans with (l' := [2; 5; 6; 8; 10; 12; 14; 19; 22; 8]%Z).
    + apply Permutation_sym.
      apply Permutation_cons_append with (l := [5; 6; 8; 10; 12; 14; 19; 22; 8]%Z).
    + apply perm_skip.
      do 3 apply perm_skip.
      apply Permutation_trans with (l' := [8; 10; 12; 14; 19; 22]%Z).
      * apply Permutation_sym.
        apply Permutation_cons_append with (l := [10; 12; 14; 19; 22]%Z).
      * apply perm_skip. apply Permutation_refl.
  - split.
    + repeat constructor; try lia.
    + split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.