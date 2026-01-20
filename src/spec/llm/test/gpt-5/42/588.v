Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [1.5%R; 0.5071788072948802%R; 3.8%R; -2.707945416165158%R; 7.9%R; -2.8003143062363973%R]
    [2.5%R; 1.5071788072948802%R; 4.8%R; -1.707945416165158%R; 8.9%R; -1.8003143062363973%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace 2.5%R with (1.5%R + 1%R) by lra.
  replace 1.5071788072948802%R with (0.5071788072948802%R + 1%R) by lra.
  replace 4.8%R with (3.8%R + 1%R) by lra.
  replace (-1.707945416165158%R) with (-2.707945416165158%R + 1%R) by lra.
  replace 8.9%R with (7.9%R + 1%R) by lra.
  replace (-1.8003143062363973%R) with (-2.8003143062363973%R + 1%R) by lra.
  reflexivity.
Qed.