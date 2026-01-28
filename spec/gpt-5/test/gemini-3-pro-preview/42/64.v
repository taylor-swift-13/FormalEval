Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_1 : incr_list_spec 
  [-0.6821906440453559%R; 0.3%R; -0.6821906440453559%R; -0.6821906440453559%R] 
  [0.3178093559546441%R; 1.3%R; 0.3178093559546441%R; 0.3178093559546441%R].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat f_equal; lra.
Qed.