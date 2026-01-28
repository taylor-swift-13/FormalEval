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
  problem_21_spec [(-10)%R; 0%R; 10%R; (5218127444499308/10000000000000000)%R]
                  [0%R;
                   ((0 - (-10)) / (10 - (-10)));
                   1%R;
                   (((5218127444499308/10000000000000000) - (-10)) / (10 - (-10)))].
Proof.
  unfold problem_21_spec.
  exists (-10)%R, 10%R.
  split.
  - unfold is_list_min. split.
    + simpl; auto.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [Hx | Hx].
      * subst; lra.
      * destruct Hx as [Hx | Hx].
        { subst; lra. }
        { destruct Hx as [Hx | Hx].
          - subst; lra.
          - destruct Hx as [Hx | Hx].
            + subst; lra.
            + contradiction. }
  - split.
    + unfold is_list_max. split.
      * simpl; auto.
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
              * contradiction. }
    + simpl.
      unfold Rdiv.
      apply (f_equal2 (@cons R)); [ | ].
      * replace ((-10) - (-10)) with 0 by lra. rewrite Rmult_0_l. reflexivity.
      * apply (f_equal2 (@cons R)); [ | ].
        -- reflexivity.
        -- apply (f_equal2 (@cons R)); [ | ].
           ++ assert (Hnz: (10 - (-10)) <> 0) by (apply Rgt_not_eq; lra).
              rewrite Rinv_r by exact Hnz. reflexivity.
           ++ apply (f_equal2 (@cons R)); [ | ].
              ** reflexivity.
              ** reflexivity.
Qed.