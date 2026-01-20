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

Example test_median : median_spec [1; 1; 20; 2; 3; 6; 99; 4; 4; 1; 2]%Z (inject_Z 3).
Proof.
  unfold median_spec.
  exists [1; 1; 1; 2; 2; 3; 4; 4; 6; 20; 99]%Z.
  split.
  - apply perm_skip.
    apply perm_skip.
    change [20; 2; 3; 6; 99; 4; 4; 1; 2]%Z with ([20; 2; 3; 6; 99; 4; 4] ++ 1 :: [2])%Z.
    apply Permutation_trans with (l' := (1 :: [20; 2; 3; 6; 99; 4; 4] ++ [2])%Z).
    + apply Permutation_sym, Permutation_middle.
    + apply perm_skip. simpl.
      change [20; 2; 3; 6; 99; 4; 4; 2]%Z with ([20] ++ 2 :: [3; 6; 99; 4; 4; 2])%Z.
      apply Permutation_trans with (l' := (2 :: [20] ++ [3; 6; 99; 4; 4; 2])%Z).
      * apply Permutation_sym, Permutation_middle.
      * apply perm_skip. simpl.
        change [20; 3; 6; 99; 4; 4; 2]%Z with ([20; 3; 6; 99; 4; 4] ++ 2 :: [])%Z.
        apply Permutation_trans with (l' := (2 :: [20; 3; 6; 99; 4; 4] ++ [])%Z).
        { apply Permutation_sym, Permutation_middle. }
        apply perm_skip. simpl.
        change [20; 3; 6; 99; 4; 4]%Z with ([20] ++ 3 :: [6; 99; 4; 4])%Z.
        apply Permutation_trans with (l' := (3 :: [20] ++ [6; 99; 4; 4])%Z).
        { apply Permutation_sym, Permutation_middle. }
        apply perm_skip. simpl.
        change [20; 6; 99; 4; 4]%Z with ([20; 6; 99] ++ 4 :: [4])%Z.
        apply Permutation_trans with (l' := (4 :: [20; 6; 99] ++ [4])%Z).
        { apply Permutation_sym, Permutation_middle. }
        apply perm_skip. simpl.
        change [20; 6; 99; 4]%Z with ([20; 6; 99] ++ 4 :: [])%Z.
        apply Permutation_trans with (l' := (4 :: [20; 6; 99] ++ [])%Z).
        { apply Permutation_sym, Permutation_middle. }
        apply perm_skip. simpl.
        change [20; 6; 99]%Z with ([20] ++ 6 :: [99])%Z.
        apply Permutation_trans with (l' := (6 :: [20] ++ [99])%Z).
        { apply Permutation_sym, Permutation_middle. }
        apply perm_skip. simpl.
        apply perm_skip.
        apply perm_skip.
        reflexivity.
  - split.
    + repeat constructor; try lia.
    + split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.