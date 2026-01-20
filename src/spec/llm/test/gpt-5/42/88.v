Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1%R) l.

Example incr_list_spec_case :
  incr_list_spec
    [3.5747542777313726%R; 3.7%R; 8.9%R; 0.5%R; 8.9%R]
    [4.5747542777313726%R; 4.7%R; 9.9%R; 1.5%R; 9.9%R].
Proof.
  unfold incr_list_spec.
  simpl.
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  apply f_equal2; [lra|].
  reflexivity.
Qed.