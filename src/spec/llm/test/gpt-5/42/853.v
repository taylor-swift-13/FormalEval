Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1%R) l.

Example incr_list_spec_case :
  incr_list_spec
    [(-2.417196937882896)%R; (-2)%R; (-0.5)%R; 1%R; 3.2%R; 5.9%R; 7.9%R]
    [(-1.417196937882896)%R; (-1)%R; 0.5%R; 2%R; 4.2%R; 6.9%R; 8.9%R].
Proof.
  unfold incr_list_spec.
  simpl.
  apply (f_equal2 (@cons R)); [lra|].
  apply (f_equal2 (@cons R)); [lra|].
  apply (f_equal2 (@cons R)); [lra|].
  apply (f_equal2 (@cons R)); [lra|].
  apply (f_equal2 (@cons R)); [lra|].
  apply (f_equal2 (@cons R)); [lra|].
  apply (f_equal2 (@cons R)); [lra|].
  reflexivity.
Qed.