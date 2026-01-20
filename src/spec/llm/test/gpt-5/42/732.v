Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_example :
  incr_list_spec
    [3.8%R; -2.1%R; 9.406367499891232%R; 3.2%R; 7.9%R]
    [4.8%R; -1.1%R; 10.406367499891232%R; 4.2%R; 8.9%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace 4.8%R with (3.8%R + 1) by lra.
  replace (-1.1%R) with (-2.1%R + 1) by lra.
  replace 10.406367499891232%R with (9.406367499891232%R + 1) by lra.
  replace 4.2%R with (3.2%R + 1) by lra.
  replace 8.9%R with (7.9%R + 1) by lra.
  reflexivity.
Qed.