Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
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

Example test_triples_sum_to_zero_2 :
  problem_40_spec [2%Z; 3%Z; -5%Z; 0%Z; 1%Z; -1%Z] true.
Proof.
  unfold problem_40_spec.
  split.
  - intros _. reflexivity.
  - intros _.
    exists 0%nat, 2%nat, 1%nat.
    simpl.
    repeat split; lia.
Qed.