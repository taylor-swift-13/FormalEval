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

Example test_median : median_spec [1; 3; -1; 7; 8; 0; 10; 10; 8]%Z (inject_Z 7).
Proof.
  unfold median_spec.
  exists [-1; 0; 1; 3; 7; 8; 8; 10; 10]%Z.
  split.
  - (* Prove Permutation *)
    apply Permutation_sym.
    change [1; 3; -1; 7; 8; 0; 10; 10; 8]%Z with ([1; 3]%Z ++ (-1)%Z :: [7; 8; 0; 10; 10; 8]%Z).
    apply Permutation_cons_app.
    simpl.
    change [1; 3; 7; 8; 0; 10; 10; 8]%Z with ([1; 3; 7; 8]%Z ++ 0%Z :: [10; 10; 8]%Z).
    apply Permutation_cons_app.
    simpl.
    change [1; 3; 7; 8; 10; 10; 8]%Z with ([] ++ 1%Z :: [3; 7; 8; 10; 10; 8]%Z).
    apply Permutation_cons_app.
    simpl.
    change [3; 7; 8; 10; 10; 8]%Z with ([] ++ 3%Z :: [7; 8; 10; 10; 8]%Z).
    apply Permutation_cons_app.
    simpl.
    change [7; 8; 10; 10; 8]%Z with ([] ++ 7%Z :: [8; 10; 10; 8]%Z).
    apply Permutation_cons_app.
    simpl.
    change [8; 10; 10; 8]%Z with ([] ++ 8%Z :: [10; 10; 8]%Z).
    apply Permutation_cons_app.
    simpl.
    change [10; 10; 8]%Z with ([10; 10]%Z ++ 8%Z :: []).
    apply Permutation_cons_app.
    simpl.
    apply Permutation_refl.
  - split.
    + (* Prove Sorted *)
      repeat constructor; try lia.
    + (* Prove Result *)
      split.
      * simpl. lia.
      * simpl. reflexivity.
Qed.