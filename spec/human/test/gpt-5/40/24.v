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

Definition l : list Z := [-2%Z; -1%Z].

Lemma lt_2_cases : forall n, (n < 2)%nat -> n = 0%nat \/ n = 1%nat.
Proof.
  intros n H.
  destruct n as [|n]; [left; reflexivity|].
  destruct n as [|n]; [right; reflexivity|].
  simpl in H; lia.
Qed.

Example problem_40_test_case_1 :
  problem_40_spec l false.
Proof.
  unfold problem_40_spec.
  split.
  - intros Hex. exfalso.
    destruct Hex as [i [j [k [Hij [Hik [Hjk [Hi [Hj [Hk Hz]]]]]]]]].
    destruct (lt_2_cases i Hi) as [Hi0 | Hi1].
    + subst i.
      destruct (lt_2_cases j Hj) as [Hj0 | Hj1].
      * subst j. apply Hij. reflexivity.
      * subst j.
        destruct (lt_2_cases k Hk) as [Hk0 | Hk1].
        -- subst k. apply Hik. reflexivity.
        -- subst k. apply Hjk. reflexivity.
    + subst i.
      destruct (lt_2_cases j Hj) as [Hj0 | Hj1].
      * subst j.
        destruct (lt_2_cases k Hk) as [Hk0 | Hk1].
        -- subst k. apply Hjk. reflexivity.
        -- subst k. apply Hik. reflexivity.
      * subst j. apply Hij. reflexivity.
  - intros Hfeq. exfalso. discriminate Hfeq.
Qed.