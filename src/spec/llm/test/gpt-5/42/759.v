Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [-3.4%R; (-2)%R; -0.5%R; 7.9%R; 7%R; 5.9%R; 7.9%R]
    [-2.4%R; (-1)%R; 0.5%R; 8.9%R; 8%R; 6.9%R; 8.9%R].
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
  reflexivity.
Qed.