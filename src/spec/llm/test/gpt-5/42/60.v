Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1%R) l.

Example incr_list_spec_case :
  incr_list_spec
    [-0.6821906440453559%R; -0.7691785226568567%R; -0.6821906440453559%R; -0.6821906440453559%R]
    [0.3178093559546441%R; 0.2308214773431433%R; 0.3178093559546441%R; 0.3178093559546441%R].
Proof.
  unfold incr_list_spec.
  simpl.
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  reflexivity.
Qed.