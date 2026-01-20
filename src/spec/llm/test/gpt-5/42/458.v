Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [-0.5%R; 0%R; 4.228643506945893%R; 8.6%R; 5.9%R; 7.041313375938212%R; 5.9%R; 5.9%R]
    [0.5%R; 1%R; 5.228643506945893%R; 9.6%R; 6.9%R; 8.041313375938212%R; 6.9%R; 6.9%R].
Proof.
  unfold incr_list_spec.
  simpl.
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra| reflexivity].
Qed.