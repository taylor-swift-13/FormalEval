Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1%R) l.

Example incr_list_spec_case :
  incr_list_spec [0.1%R; 0.2%R] [1.1%R; 1.2%R].
Proof.
  unfold incr_list_spec.
  simpl.
  assert (0.1%R + 1%R = 1.1%R) by lra.
  assert (0.2%R + 1%R = 1.2%R) by lra.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.