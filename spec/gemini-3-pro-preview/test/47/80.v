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

Lemma perm_move_head : forall (A : Type) (x : A) (l1 l2 : list A), Permutation (l1 ++ x :: l2) (x :: l1 ++ l2).
Proof.
  intros. apply Permutation_sym. apply Permutation_middle.
Qed.

Example test_median : median_spec [1; 4; 1; 8; 2; 8; 3; 5; 1]%Z (inject_Z 3).
Proof.
  unfold median_spec.
  exists [1; 1; 1; 2; 3; 4; 5; 8; 8]%Z.
  split.
  - (* Prove Permutation *)
    apply perm_skip.
    change [4; 1; 8; 2; 8; 3; 5; 1]%Z with ([4]%Z ++ 1%Z :: [8; 2; 8; 3; 5; 1]%Z).
    apply Permutation_trans with (l' := (1 :: [4; 8; 2; 8; 3; 5; 1])%Z).
    { apply perm_move_head. }
    apply perm_skip.
    change [4; 8; 2; 8; 3; 5; 1]%Z with ([4; 8; 2; 8; 3; 5]%Z ++ 1%Z :: []).
    apply Permutation_trans with (l' := (1 :: [4; 8; 2; 8; 3; 5])%Z).
    { apply perm_move_head. }
    apply perm_skip.
    change [4; 8; 2; 8; 3; 5]%Z with ([4; 8]%Z ++ 2%Z :: [8; 3; 5]%Z).
    apply Permutation_trans with (l' := (2 :: [4; 8; 8; 3; 5])%Z).
    { apply perm_move_head. }
    apply perm_skip.
    change [4; 8; 8; 3; 5]%Z with ([4; 8; 8]%Z ++ 3%Z :: [5]%Z).
    apply Permutation_trans with (l' := (3 :: [4; 8; 8; 5])%Z).
    { apply perm_move_head. }
    apply perm_skip.
    apply perm_skip.
    change [8; 8; 5]%Z with ([8; 8]%Z ++ 5%Z :: []).
    apply Permutation_trans with (l' := (5 :: [8; 8])%Z).
    { apply perm_move_head. }
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