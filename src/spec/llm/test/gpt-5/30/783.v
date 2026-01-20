Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool := if Rlt_dec y x then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0) l.

Example get_positive_spec_test :
  get_positive_spec [-1.3426789806479305%R; 32.97170491287429%R; -2.25%R] [32.97170491287429%R].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold Rgtb at 1.
  destruct (Rlt_dec 0%R (-1.3426789806479305%R)).
  - exfalso; lra.
  - simpl.
    unfold Rgtb at 1.
    destruct (Rlt_dec 0%R (32.97170491287429%R)).
    + simpl.
      unfold Rgtb at 1.
      destruct (Rlt_dec 0%R (-2.25%R)).
      * exfalso; lra.
      * simpl; reflexivity.
    + exfalso; lra.
Qed.