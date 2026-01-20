Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [-3.4%R; 10.746488790862529%R; 0%R; 3.2%R; -0.5%R; 5.9%R; 7.780292177637895%R; 5.9%R; 5.9%R; 3.2%R]
    [-2.4%R; 11.746488790862529%R; 1%R; 4.2%R; 0.5%R; 6.9%R; 8.780292177637895%R; 6.9%R; 6.9%R; 4.2%R].
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
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|reflexivity].
Qed.