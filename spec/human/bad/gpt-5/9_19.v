Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example problem_9_test_0 :
  problem_9_spec
    [0%Z; 4%Z; -3%Z; -4%Z; -5%Z; -4%Z; -3%Z; -2%Z; -1%Z]
    [0%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z].
Proof.
  unfold problem_9_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [|i'].
    + split.
      * intros j Hj.
        assert (j = 0)%nat by lia.
        subst.
        simpl.
        lia.
      * exists 0%nat.
        split; [lia| reflexivity].
    + assert (Hi8 : (i' < 8)%nat) by lia.
      split.
      * intros j Hj.
        assert (Hj9 : (j < 9)%nat) by lia.
        assert (Hout_eq4 :
                  nth (S i') [0%Z;4%Z;4%Z;4%Z;4%Z;4%Z;4%Z;4%Z;4%Z] 0 = 4%Z).
        { revert Hi8.
          destruct i' as [|i1]; intros; simpl; [reflexivity|].
          destruct i1 as [|i2]; simpl; [reflexivity|].
          destruct i2 as [|i3]; simpl; [reflexivity|].
          destruct i3 as [|i4]; simpl; [reflexivity|].
          destruct i4 as [|i5]; simpl; [reflexivity|].
          destruct i5 as [|i6]; simpl; [reflexivity|].
          destruct i6 as [|i7]; simpl; [reflexivity|].
          destruct i7; simpl; [reflexivity|].
          lia.
        }
        assert (Hinp_le4 :
                  forall k, (k < 9)%nat ->
                            nth k [0%Z;4%Z;-3%Z;-4%Z;-5%Z;-4%Z;-3%Z;-2%Z;-1%Z] 0 <= 4%Z).
        { intros k Hk.
          destruct k as [|k1]; simpl; [lia|].
          destruct k1 as [|k2]; simpl; [lia|].
          destruct k2 as [|k3]; simpl; [lia|].
          destruct k3 as [|k4]; simpl; [lia|].
          destruct k4 as [|k5]; simpl; [lia|].
          destruct k5 as [|k6]; simpl; [lia|].
          destruct k6 as [|k7]; simpl; [lia|].
          destruct k7 as [|k8]; simpl; [lia|].
          destruct k8; simpl; lia.
        }
        specialize (Hinp_le4 j Hj9).
        rewrite Hout_eq4.
        exact Hinp_le4.
      * exists 1%nat.
        split.
        { lia. }
        assert (Hout_eq4 :
                  nth (S i') [0%Z;4%Z;4%Z;4%Z;4%Z;4%Z;4%Z;4%Z;4%Z] 0 = 4%Z).
        { revert Hi8.
          destruct i' as [|i1]; intros; simpl; [reflexivity|].
          destruct i1 as [|i2]; simpl; [reflexivity|].
          destruct i2 as [|i3]; simpl; [reflexivity|].
          destruct i3 as [|i4]; simpl; [reflexivity|].
          destruct i4 as [|i5]; simpl; [reflexivity|].
          destruct i5 as [|i6]; simpl; [reflexivity|].
          destruct i6 as [|i7]; simpl; [reflexivity|].
          destruct i7; simpl; [reflexivity|].
          lia.
        }
        simpl.
        rewrite Hout_eq4.
        reflexivity.
Qed.