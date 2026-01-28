Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope Q_scope.

Definition median_spec (l : list Q) (res : Q) : Prop :=
  exists sorted_l,
    Permutation l sorted_l /\
    Sorted Qle sorted_l /\
    let n := length l in
    (n > 0)%nat /\
    if Nat.odd n then
      res == nth (n / 2) sorted_l (0#1)
    else
      res == Qdiv (Qplus (nth (n / 2 - 1) sorted_l (0#1)) 
                        (nth (n / 2) sorted_l (0#1))) 
                 (2#1).

Example test_median : median_spec [7#2; 57#10; 61#10; 36#5; 10#1; 13#1; 29#2; 84#5; 197#10; 61#10] (43#5).
Proof.
  unfold median_spec.
  exists [7#2; 57#10; 61#10; 61#10; 36#5; 10#1; 13#1; 29#2; 84#5; 197#10].
  split.
  - repeat apply perm_skip.
    assert (H: Permutation ([36#5; 10#1; 13#1; 29#2; 84#5; 197#10] ++ [61#10]) ([61#10] ++ [36#5; 10#1; 13#1; 29#2; 84#5; 197#10])).
    { apply Permutation_app_comm. }
    simpl in H. apply H.
  - split.
    + repeat constructor; try (unfold Qle; simpl; lia).
    + split.
      * simpl. lia.
      * simpl. unfold Qeq. simpl. lia.
Qed.