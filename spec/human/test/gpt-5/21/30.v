Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Lra.

Import ListNotations.

Open Scope R_scope.

Definition is_list_min (l : list R) (m : R) : Prop :=
  In m l /\ (forall x, In x l -> m <= x).

Definition is_list_max (l : list R) (m : R) : Prop :=
  In m l /\ (forall x, In x l -> m >= x).

Definition problem_21_pre (input : list R) : Prop := (length input >= 2)%nat.

Definition problem_21_spec (input output : list R) : Prop :=
  exists min_val max_val,
    is_list_min input min_val /\
    is_list_max input max_val /\
    (output = map (fun x => (x - min_val) / (max_val - min_val)) input).

Example problem_21_test :
  problem_21_spec [5%R; 2%R; 2%R; 5%R; 2%R; 5%R] [1%R; 0%R; 0%R; 1%R; 0%R; 1%R].
Proof.
  unfold problem_21_spec.
  exists 2%R, 5%R.
  split.
  - unfold is_list_min. split.
    + simpl; right; left; reflexivity.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [Hx | Hx].
      * subst; lra.
      * destruct Hx as [Hx | Hx].
        { subst; lra. }
        { destruct Hx as [Hx | Hx].
          - subst; lra.
          - destruct Hx as [Hx | Hx].
            { subst; lra. }
            { destruct Hx as [Hx | Hx].
              - subst; lra.
              - destruct Hx as [Hx | Hx].
                + subst; lra.
                + contradiction. } }
  - split.
    + unfold is_list_max. split.
      * simpl; left; reflexivity.
      * intros x Hx.
        simpl in Hx.
        destruct Hx as [Hx | Hx].
        { subst; lra. }
        { destruct Hx as [Hx | Hx].
          - subst; lra.
          - destruct Hx as [Hx | Hx].
            + subst; lra.
            + destruct Hx as [Hx | Hx].
              * subst; lra.
              * destruct Hx as [Hx | Hx].
                { subst; lra. }
                { destruct Hx as [Hx | Hx].
                  - subst; lra.
                  - contradiction. } }
    + simpl.
      unfold Rdiv.
      assert (Hnz: (5 - 2) <> 0) by (apply Rgt_not_eq; lra).
      apply (f_equal2 (@cons R)); [ | ].
      * rewrite Rinv_r by exact Hnz. reflexivity.
      * apply (f_equal2 (@cons R)); [ | ].
        -- replace (2 - 2) with 0 by lra. rewrite Rmult_0_l. reflexivity.
        -- apply (f_equal2 (@cons R)); [ | ].
           ++ replace (2 - 2) with 0 by lra. rewrite Rmult_0_l. reflexivity.
           ++ apply (f_equal2 (@cons R)); [ | ].
              ** rewrite Rinv_r by exact Hnz. reflexivity.
              ** apply (f_equal2 (@cons R)); [ | ].
                 --- replace (2 - 2) with 0 by lra. rewrite Rmult_0_l. reflexivity.
                 --- apply (f_equal2 (@cons R)); [ | ].
                     +++ rewrite Rinv_r by exact Hnz. reflexivity.
                     +++ reflexivity.
Qed.