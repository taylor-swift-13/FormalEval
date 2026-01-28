Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Lia.
Import ListNotations.
Open Scope R_scope.

Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_below_threshold_1 : problem_52_spec [3.5; 2.2; 1.1] 5 true.
Proof.
  unfold problem_52_spec.
  split.
  - intros H. reflexivity.
  - intros H x Hx.
    simpl in Hx.
    destruct Hx as [Hx | [Hx | [Hx | Hx]]].
    + subst x. unfold IZR. simpl. 
      apply Rlt_trans with 4.
      * apply Rlt_trans with 3.6.
        -- unfold Rdiv. rewrite Rmult_comm.
           apply Rmult_lt_compat_r with (r := /10).
           ++ apply Rinv_0_lt_compat. 
              repeat (apply Rplus_lt_0_compat || apply Rlt_0_1).
           ++ rewrite Rinv_r.
              ** apply Rlt_trans with 36.
                 --- repeat (apply Rplus_lt_compat || apply Rlt_0_1 || apply Rle_refl).
                     repeat apply Rplus_lt_compat_l. apply Rlt_0_1.
                 --- repeat (apply Rplus_lt_compat || apply Rlt_0_1).
                     repeat apply Rplus_lt_compat_l. apply Rlt_0_1.
              ** apply Rgt_not_eq.
                 repeat (apply Rplus_lt_0_compat || apply Rlt_0_1).
        -- repeat (apply Rplus_lt_compat || apply Rlt_0_1).
           apply Rplus_lt_compat_l. apply Rlt_0_1.
      * repeat (apply Rplus_lt_compat || apply Rlt_0_1).
        apply Rplus_lt_compat_l. apply Rlt_0_1.
    + subst x.
      apply Rlt_trans with 3.
      * apply Rlt_trans with 2.3.
        -- repeat (apply Rplus_lt_compat || apply Rlt_0_1).
           apply Rplus_lt_compat_l. apply Rlt_0_1.
        -- repeat (apply Rplus_lt_compat || apply Rlt_0_1).
           apply Rplus_lt_compat_l. apply Rlt_0_1.
      * repeat (apply Rplus_lt_compat || apply Rlt_0_1).
        repeat apply Rplus_lt_compat_l. apply Rlt_0_1.
    + subst x.
      apply Rlt_trans with 2.
      * apply Rlt_trans with 1.2.
        -- repeat (apply Rplus_lt_compat || apply Rlt_0_1).
           apply Rplus_lt_compat_l. apply Rlt_0_1.
        -- repeat (apply Rplus_lt_compat || apply Rlt_0_1).
           apply Rplus_lt_compat_l. apply Rlt_0_1.
      * repeat (apply Rplus_lt_compat || apply Rlt_0_1).
        repeat apply Rplus_lt_compat_l. apply Rlt_0_1.
    + contradiction.
Qed.