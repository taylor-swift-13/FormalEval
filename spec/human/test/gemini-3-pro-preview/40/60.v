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

Example test_case : problem_40_spec [10; -20; 30; -20; 6; -40; 50; -60; 10; -40] true.
Proof.
  unfold problem_40_spec.
  split.
  - intros. reflexivity.
  - intros.
    exists 0%nat, 1%nat, 8%nat.
    simpl.
    repeat split; try lia.
Qed.