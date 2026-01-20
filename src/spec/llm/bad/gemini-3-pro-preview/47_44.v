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

Example test_median : median_spec [10; 20; 4; 30; 13; 2; 40; 50]%Z (33#2).
Proof.
  unfold median_spec.
  exists [2; 4; 10; 13; 20; 30; 40; 50]%Z.
  split.
  - (* Permutation *)
    (* Move 10 *)
    apply Permutation_trans with (l' := (10 :: [2; 4] ++ [13; 20; 30; 40; 50])%Z).
    2: apply Permutation_middle.
    apply perm_skip.
    (* Move 20 *)
    apply Permutation_trans with (l' := (20 :: [2; 4; 13] ++ [30; 40; 50])%Z).
    2: apply Permutation_middle.
    apply perm_skip.
    (* Move 4 *)
    apply Permutation_trans with (l' := (4 :: [2] ++ [13; 30; 40; 50])%Z).
    2: apply Permutation_middle.
    apply perm_skip.
    (* Move 30 *)
    apply Permutation_trans with (l' := (30 :: [2; 13] ++ [40; 50])%Z).
    2: apply Permutation_middle.
    apply perm_skip.
    (* Move 13 *)
    apply Permutation_trans with (l' := (13 :: [2] ++ [40; 50])%Z).
    2: apply Permutation_middle.
    apply perm_skip.
    (* Move 2 *)
    apply Permutation_trans with (l' := (2 :: [] ++ [40; 50])%Z).
    2: apply Permutation_middle.
    apply perm_skip.
    (* Move 40 *)
    apply Permutation_trans with (l' := (40 :: [] ++ [50])%Z).
    2: apply Permutation_middle.
    apply perm_skip.
    (* Move 50 *)
    apply Permutation_refl.
  - split.
    + (* Sorted *)
      repeat constructor; try lia.
    + (* Result *)
      split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.