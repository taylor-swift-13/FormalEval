Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_decimals :
  incr_list_spec [0.1%R; 0.3%R; 0.1%R] [1.1%R; 1.3%R; 1.1%R].
Proof.
  unfold incr_list_spec.
  simpl.
  assert (H1 : 0.1%R + 1%R = 1.1%R) by lra.
  assert (H2 : 0.3%R + 1%R = 1.3%R) by lra.
  rewrite H2.
  repeat rewrite H1.
  reflexivity.
Qed.