Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_R : list R -> list R -> Prop :=
| gp_nil : get_positive_R [] []
| gp_pos : forall x l l', x > 0 -> get_positive_R l l' -> get_positive_R (x :: l) (x :: l')
| gp_neg : forall x l l', x <= 0 -> get_positive_R l l' -> get_positive_R (x :: l) l'.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_R l res.

Example test_get_positive : get_positive_spec [-1.3426789806479305; 32.97170491287429; -2.25] [32.97170491287429].
Proof.
  unfold get_positive_spec.
  apply gp_neg.
  - lra.
  - apply gp_pos.
    + lra.
    + apply gp_neg.
      * lra.
      * apply gp_nil.
Qed.