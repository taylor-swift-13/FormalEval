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

Example test_median : median_spec [1; 1; 2; 2; 3; 4; 1; 3; 4]%Z (inject_Z 2).
Proof.
  unfold median_spec.
  exists [1; 1; 1; 2; 2; 3; 3; 4; 4]%Z.
  split.
  - apply perm_skip. apply perm_skip.
    apply Permutation_trans with (l' := (1 :: [2; 2; 3; 4] ++ [3; 4])%Z).
    + apply Permutation_sym. apply Permutation_middle.
    + simpl. apply perm_skip.
      apply perm_skip. apply perm_skip.
      apply perm_skip.
      apply Permutation_trans with (l' := (3 :: [4] ++ [4])%Z).
      * apply Permutation_sym. apply Permutation_middle.
      * simpl. repeat constructor.
  - split.
    + repeat constructor; try lia.
    + split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.