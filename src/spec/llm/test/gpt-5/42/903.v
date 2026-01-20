Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [-3.4%R; -2%R; -0.5%R; 1%R; 3.2%R; 5.9%R; -3.4%R]
    [-2.4%R; -1%R; 0.5%R; 2%R; 4.2%R; 6.9%R; -2.4%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace (-3.4%R + 1%R) with (-2.4%R) by lra.
  replace (-2%R + 1%R) with (-1%R) by lra.
  replace (-0.5%R + 1%R) with (0.5%R) by lra.
  replace (1%R + 1%R) with (2%R) by lra.
  replace (3.2%R + 1%R) with (4.2%R) by lra.
  replace (5.9%R + 1%R) with (6.9%R) by lra.
  reflexivity.
Qed.