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

Example test_median : median_spec [-5; 51; 50; 0; 3; 6]%Z (9#2).
Proof.
  unfold median_spec.
  exists [-5; 0; 3; 6; 50; 51]%Z.
  split.
  - (* Prove Permutation *)
    apply perm_skip.
    apply Permutation_trans with (l' := [0; 51; 50; 3; 6]%Z).
    + apply Permutation_trans with (l' := [51; 0; 50; 3; 6]%Z).
      * apply perm_skip. apply perm_swap.
      * apply perm_swap.
    + apply perm_skip.
      apply Permutation_trans with (l' := [3; 51; 50; 6]%Z).
      * apply Permutation_trans with (l' := [51; 3; 50; 6]%Z).
        -- apply perm_skip. apply perm_swap.
        -- apply perm_swap.
      * apply perm_skip.
        apply Permutation_trans with (l' := [6; 51; 50]%Z).
        -- apply Permutation_trans with (l' := [51; 6; 50]%Z).
           ++ apply perm_skip. apply perm_swap.
           ++ apply perm_swap.
        -- apply perm_skip. apply perm_swap.
  - split.
    + (* Prove Sorted *)
      repeat constructor; try lia.
    + (* Prove Result *)
      split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.