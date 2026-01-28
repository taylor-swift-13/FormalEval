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

Definition l : list Z := [1%Z; 2%Z; 5%Z; 7%Z].

Lemma nth_pos_in_l : forall idx, (idx < length l)%nat -> 1 <= nth idx l 0.
Proof.
  intros idx Hlt.
  unfold l in *; simpl in *.
  destruct idx as [|idx]; simpl in *.
  - lia.
  - destruct idx as [|idx]; simpl in *.
    + lia.
    + destruct idx as [|idx]; simpl in *.
      * lia.
      * destruct idx as [|idx]; simpl in *.
        -- lia.
        -- exfalso. lia.
Qed.

Example problem_40_test_case_1 :
  problem_40_spec l false.
Proof.
  unfold problem_40_spec.
  split.
  - intros Hex. exfalso.
    destruct Hex as [i [j [k [Hij [Hik [Hjk [Hi [Hj [Hk Hz]]]]]]]]].
    pose proof (nth_pos_in_l i Hi) as Hi_pos.
    pose proof (nth_pos_in_l j Hj) as Hj_pos.
    pose proof (nth_pos_in_l k Hk) as Hk_pos.
    assert (Hsum: 3 <= nth i l 0 + nth j l 0 + nth k l 0) by lia.
    rewrite Hz in Hsum. lia.
  - intros Hfeq. exfalso. discriminate Hfeq.
Qed.