Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no additional constraints for `triples_sum_to_zero` by default *)
Definition problem_40_pre (input : list Z) : Prop := True.

Definition problem_40_spec (input : list Z) (output : bool) : Prop :=
  (exists i j k : nat,
    (i <> j) /\ (i <> k) /\ (j <> k) /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (k < length input)%nat /\
    (nth i input 0 + nth j input 0 + nth k input 0 = 0))
  <-> (output = true).

Definition l : list Z := [1%Z; 3%Z; 5%Z; 0%Z].

(* Elements of l at valid indices are nonnegative *)
Lemma nth_nonneg_in_l : forall idx, (idx < length l)%nat -> 0 <= nth idx l 0.
Proof.
  intros idx Hlt.
  unfold l in *; simpl in *.
  destruct idx as [|idx]; simpl; try lia.
  destruct idx as [|idx]; simpl; try lia.
  destruct idx as [|idx]; simpl; try lia.
  destruct idx as [|idx]; simpl in *.
  - lia.
  - exfalso. lia.
Qed.

(* The only valid index where nth i l 0 = 0 is i = 3 *)
Lemma nth_eq0_index3 :
  forall i, (i < length l)%nat -> nth i l 0 = 0 -> i = 3%nat.
Proof.
  intros i Hi Hz.
  unfold l in *; simpl in *.
  destruct i as [|i]; simpl in *.
  - exfalso. lia.
  - destruct i as [|i]; simpl in *.
    + exfalso. lia.
    + destruct i as [|i]; simpl in *.
      * exfalso. lia.
      * destruct i as [|i]; simpl in *.
        -- reflexivity.
        -- exfalso. lia.
Qed.

Example problem_40_test_case_1 :
  problem_40_spec l false.
Proof.
  unfold problem_40_spec.
  split.
  - intros Hex. exfalso.
    destruct Hex as [i [j [k [Hij [Hik [Hjk [Hi [Hj [Hk Hz]]]]]]]]].
    pose proof (nth_nonneg_in_l i Hi) as Hi_nonneg.
    pose proof (nth_nonneg_in_l j Hj) as Hj_nonneg.
    pose proof (nth_nonneg_in_l k Hk) as Hk_nonneg.
    assert (Hi0: nth i l 0 = 0) by lia.
    assert (Hj0: nth j l 0 = 0) by lia.
    assert (Hk0: nth k l 0 = 0) by lia.
    pose proof (nth_eq0_index3 i Hi Hi0) as Hi3.
    pose proof (nth_eq0_index3 j Hj Hj0) as Hj3.
    pose proof (nth_eq0_index3 k Hk Hk0) as Hk3.
    rewrite Hi3, Hj3 in Hij.
    apply Hij. reflexivity.
  - intros Hfeq. exfalso. discriminate Hfeq.
Qed.