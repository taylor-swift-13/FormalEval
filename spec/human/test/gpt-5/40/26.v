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

Definition l : list Z := [1%Z; -2%Z; -4%Z].

Lemma lt3_cases : forall n, (n < 3)%nat -> n = 0%nat \/ n = 1%nat \/ n = 2%nat.
Proof.
  intros n H.
  destruct n as [|n].
  - now left.
  - destruct n as [|n].
    + now right; left.
    + destruct n as [|n].
      * now right; right.
      * exfalso; lia.
Qed.

Example problem_40_test_case_1 :
  problem_40_spec l false.
Proof.
  unfold problem_40_spec.
  split.
  - intros Hex. exfalso.
    destruct Hex as [i [j [k [Hij [Hik [Hjk [Hi [Hj [Hk Hz]]]]]]]]].
    assert (Hlen: length l = 3%nat) by (unfold l; reflexivity).
    rewrite Hlen in Hi, Hj, Hk.
    destruct (lt3_cases i Hi) as [Hi0 | [Hi1 | Hi2]].
    + subst i.
      destruct (lt3_cases j Hj) as [Hj0 | [Hj1 | Hj2]].
      * subst j. contradiction.
      * subst j.
        destruct (lt3_cases k Hk) as [Hk0 | [Hk1 | Hk2]].
        -- subst k. contradiction.
        -- subst k. contradiction.
        -- subst k. unfold l in Hz; simpl in Hz; lia.
      * subst j.
        destruct (lt3_cases k Hk) as [Hk0 | [Hk1 | Hk2]].
        -- subst k. contradiction.
        -- subst k. unfold l in Hz; simpl in Hz; lia.
        -- subst k. contradiction.
    + subst i.
      destruct (lt3_cases j Hj) as [Hj0 | [Hj1 | Hj2]].
      * subst j.
        destruct (lt3_cases k Hk) as [Hk0 | [Hk1 | Hk2]].
        -- subst k. contradiction.
        -- subst k. contradiction.
        -- subst k. unfold l in Hz; simpl in Hz; lia.
      * subst j. contradiction.
      * subst j.
        destruct (lt3_cases k Hk) as [Hk0 | [Hk1 | Hk2]].
        -- subst k. unfold l in Hz; simpl in Hz; lia.
        -- subst k. contradiction.
        -- subst k. contradiction.
    + subst i.
      destruct (lt3_cases j Hj) as [Hj0 | [Hj1 | Hj2]].
      * subst j.
        destruct (lt3_cases k Hk) as [Hk0 | [Hk1 | Hk2]].
        -- subst k. contradiction.
        -- subst k. unfold l in Hz; simpl in Hz; lia.
        -- subst k. contradiction.
      * subst j.
        destruct (lt3_cases k Hk) as [Hk0 | [Hk1 | Hk2]].
        -- subst k. unfold l in Hz; simpl in Hz; lia.
        -- subst k. contradiction.
        -- subst k. contradiction.
      * subst j. contradiction.
  - intros Hfeq. exfalso. discriminate Hfeq.
Qed.