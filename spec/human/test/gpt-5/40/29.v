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

Definition l : list Z := [1%Z; 3%Z; -5%Z; 1%Z; -1%Z; 2%Z].

Example problem_40_test_case_1 :
  problem_40_spec l true.
Proof.
  unfold problem_40_spec.
  split.
  - intros _. reflexivity.
  - intros _. exists 1%nat, 2%nat, 5%nat.
    repeat split; try lia.
    all: unfold l; simpl; lia.
Qed.