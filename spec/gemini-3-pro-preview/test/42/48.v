Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = map (fun x => x + 1) l.

Example test_incr_list_float : incr_list_spec [-0.6821906440453559; 0.3; -0.6821906440453559] [0.3178093559546441; 1.3; 0.3178093559546441].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat (f_equal; try lra).
Qed.