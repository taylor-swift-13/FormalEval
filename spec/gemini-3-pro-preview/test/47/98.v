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

Example test_median : median_spec [10; 20; -1; 40; 50; -1]%Z (30#2).
Proof.
  unfold median_spec.
  exists [-1; -1; 10; 20; 40; 50]%Z.
  split.
  - (* Prove Permutation *)
    (* Move first -1 (index 2) to front *)
    apply Permutation_trans with (l' := [10; -1; 20; 40; 50; -1]%Z).
    { apply perm_skip. apply perm_swap. }
    apply Permutation_trans with (l' := [-1; 10; 20; 40; 50; -1]%Z).
    { apply perm_swap. }
    apply perm_skip.
    (* Move second -1 (index 4 in tail) to front of tail *)
    apply Permutation_trans with (l' := [10; 20; 40; -1; 50]%Z).
    { do 3 apply perm_skip. apply perm_swap. }
    apply Permutation_trans with (l' := [10; 20; -1; 40; 50]%Z).
    { do 2 apply perm_skip. apply perm_swap. }
    apply Permutation_trans with (l' := [10; -1; 20; 40; 50]%Z).
    { apply perm_skip. apply perm_swap. }
    apply Permutation_trans with (l' := [-1; 10; 20; 40; 50]%Z).
    { apply perm_swap. }
    apply perm_skip.
    reflexivity.
  - split.
    + (* Prove Sorted *)
      repeat constructor; try lia.
    + (* Prove Result *)
      split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.