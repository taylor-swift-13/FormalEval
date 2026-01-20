Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_example :
  incr_list_spec [3.7%R; 0.1%R; 1.2%R] [4.7%R; 1.1%R; 2.2%R].
Proof.
  unfold incr_list_spec.
  simpl.
  assert (H1: 4.7%R = 3.7%R + 1%R) by lra.
  assert (H2: 1.1%R = 0.1%R + 1%R) by lra.
  assert (H3: 2.2%R = 1.2%R + 1%R) by lra.
  rewrite H1, H2, H3.
  reflexivity.
Qed.