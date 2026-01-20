Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [9.9%R; -2.6958053769612267%R; 33.195768044846155%R; -2.25%R] [9.9%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 9.9%R) as [H1|H1].
  - simpl.
    destruct (Rlt_dec 0 (-2.6958053769612267%R)) as [H2|H2].
    + exfalso.
      assert (~ (-2.6958053769612267%R < 0%R)) by (apply (Rlt_asym 0 (-2.6958053769612267%R)); exact H2).
      apply H; lra.
    + simpl.
      destruct (Rlt_dec 0 33.195768044846155%R) as [H3|H3].
      * simpl.
        destruct (Rlt_dec 0 (-2.25%R)) as [H4|H4].
        -- exfalso.
           assert (~ (-2.25%R < 0%R)) by (apply (Rlt_asym 0 (-2.25%R)); exact H4).
           apply H; lra.
        -- simpl.
           reflexivity.
      * exfalso.
        apply H3; lra.
  - exfalso.
    apply H1; lra.
Qed.