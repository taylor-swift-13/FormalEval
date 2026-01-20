Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool := if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0) l.

Example get_positive_spec_test :
  get_positive_spec [-89.04346588476734%R; 32.97170491287429%R; -2.6958053769612267%R; 7.7%R] [32.97170491287429%R; 7.7%R].
Proof.
  unfold get_positive_spec.
  unfold Rgtb.
  simpl.
  destruct (Rgt_dec (-89.04346588476734%R) 0) as [H1|H1].
  - exfalso; lra.
  - simpl.
    destruct (Rgt_dec 32.97170491287429%R 0) as [H2|H2].
    + simpl.
      destruct (Rgt_dec (-2.6958053769612267%R) 0) as [H3|H3].
      * exfalso; lra.
      * simpl.
        destruct (Rgt_dec 7.7%R 0) as [H4|H4].
        -- simpl. reflexivity.
        -- exfalso; lra.
    + exfalso; lra.
Qed.