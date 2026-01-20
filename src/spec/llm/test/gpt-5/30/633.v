Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool := if Rlt_dec y x then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0) l.

Example get_positive_spec_test :
  get_positive_spec [-89.04346588476734%R; 32.97170491287429%R; -2.25%R] [32.97170491287429%R].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold Rgtb.
  simpl.
  destruct (Rlt_dec 0 (-89.04346588476734%R)) as [H1|H1].
  - exfalso; lra.
  - simpl.
    destruct (Rlt_dec 0 32.97170491287429%R) as [H2|H2].
    + simpl.
      destruct (Rlt_dec 0 (-2.25%R)) as [H3|H3].
      * exfalso; lra.
      * simpl. reflexivity.
    + exfalso; lra.
Qed.