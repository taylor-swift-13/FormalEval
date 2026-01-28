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

Example test_median : median_spec [10; 20; 4; 30; 13; 2; 40; 50; 30]%Z (inject_Z 20).
Proof.
  unfold median_spec.
  exists [2; 4; 10; 13; 20; 30; 30; 40; 50]%Z.
  split.
  - change [10; 20; 4; 30; 13; 2; 40; 50; 30]%Z with ([10; 20; 4; 30; 13]%Z ++ 2%Z :: [40; 50; 30]%Z).
    apply Permutation_trans with (l' := 2%Z :: ([10; 20; 4; 30; 13]%Z ++ [40; 50; 30]%Z)).
    + apply Permutation_sym. apply Permutation_middle.
    + apply perm_skip.
      change ([10; 20; 4; 30; 13]%Z ++ [40; 50; 30]%Z) with ([10; 20]%Z ++ 4%Z :: [30; 13; 40; 50; 30]%Z).
      apply Permutation_trans with (l' := 4%Z :: ([10; 20]%Z ++ [30; 13; 40; 50; 30]%Z)).
      * apply Permutation_sym. apply Permutation_middle.
      * apply perm_skip.
        apply perm_skip.
        change [20; 30; 13; 40; 50; 30]%Z with ([20; 30]%Z ++ 13%Z :: [40; 50; 30]%Z).
        apply Permutation_trans with (l' := 13%Z :: ([20; 30]%Z ++ [40; 50; 30]%Z)).
        -- apply Permutation_sym. apply Permutation_middle.
        -- apply perm_skip.
           apply perm_skip.
           apply perm_skip.
           change [40; 50; 30]%Z with ([40; 50]%Z ++ 30%Z :: []%Z).
           apply Permutation_trans with (l' := 30%Z :: ([40; 50]%Z ++ []%Z)).
           ++ apply Permutation_sym. apply Permutation_middle.
           ++ apply perm_skip.
              apply Permutation_refl.
  - split.
    + repeat constructor; try lia.
    + split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.