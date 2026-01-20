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

Example test_median : median_spec [10; 20; -1; 30; 40; 50]%Z (50 # 2).
Proof.
  unfold median_spec.
  exists [-1; 10; 20; 30; 40; 50]%Z.
  split.
  - apply Permutation_trans with (l' := [10; -1; 20; 30; 40; 50]%Z).
    + apply perm_skip. apply perm_swap.
    + apply perm_swap.
  - split.
    + repeat constructor; try lia.
    + split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.