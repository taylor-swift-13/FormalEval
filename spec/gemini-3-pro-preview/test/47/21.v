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

Example test_median : median_spec [1; 3; -1; 7; 8; 8; 10; 10; 8; 8]%Z (16#2).
Proof.
  unfold median_spec.
  exists [-1; 1; 3; 7; 8; 8; 8; 8; 10; 10]%Z.
  split.
  - (* Prove Permutation *)
    (* Step 1: Move -1 to the front *)
    apply Permutation_trans with (l' := [-1; 1; 3; 7; 8; 8; 10; 10; 8; 8]%Z).
    + apply Permutation_trans with (l' := [1; -1; 3; 7; 8; 8; 10; 10; 8; 8]%Z).
      * apply perm_skip. apply perm_swap.
      * apply perm_swap.
    + (* Skip the matching prefix: -1, 1, 3, 7, 8, 8 *)
      apply perm_skip. apply perm_skip. apply perm_skip. 
      apply perm_skip. apply perm_skip. apply perm_skip.
      (* Remaining Source: [10; 10; 8; 8] *)
      (* Remaining Target: [8; 8; 10; 10] *)
      (* Move the first 8 to front *)
      apply Permutation_trans with (l' := [8; 10; 10; 8]%Z).
      * apply Permutation_trans with (l' := [10; 8; 10; 8]%Z).
        { apply perm_skip. apply perm_swap. }
        { apply perm_swap. }
      * apply perm_skip.
        (* Remaining Source: [10; 10; 8] *)
        (* Remaining Target: [8; 10; 10] *)
        (* Move the remaining 8 to front *)
        apply Permutation_trans with (l' := [8; 10; 10]%Z).
        { apply Permutation_trans with (l' := [10; 8; 10]%Z).
          { apply perm_skip. apply perm_swap. }
          { apply perm_swap. }
        }
        reflexivity.
  - split.
    + (* Prove Sorted *)
      repeat constructor; try lia.
    + (* Prove Result *)
      split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.