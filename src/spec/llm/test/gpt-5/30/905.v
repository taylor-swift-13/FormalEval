Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rlt_dec 0 x then true else false) l.

Example get_positive_spec_test :
  get_positive_spec [-89.04346588476734%R; -2.6958053769612267%R] [].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rlt_dec 0 (-89.04346588476734%R)) as [H1|H1].
  - exfalso. lra.
  - simpl.
    destruct (Rlt_dec 0 (-2.6958053769612267%R)) as [H2|H2].
    + exfalso. lra.
    + simpl. reflexivity.
Qed.