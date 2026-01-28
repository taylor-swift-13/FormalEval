Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_40_pre (input : list Z) : Prop := True.

Definition problem_40_spec (input : list Z) (output : bool) : Prop :=
  (exists i j k : nat,
    (i <> j) /\ (i <> k) /\ (j <> k) /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (k < length input)%nat /\
    (nth i input 0 + nth j input 0 + nth k input 0 = 0))
  <-> (output = true).

Example test_case : problem_40_spec [1; 1; 2; 3; 4; 5; -9; 1; 1] true.
Proof.
  unfold problem_40_spec.
  split.
  - intros _. reflexivity.
  - intros _.
    exists 4%nat, 5%nat, 6%nat.
    repeat split; try lia.
    simpl. reflexivity.
Qed.