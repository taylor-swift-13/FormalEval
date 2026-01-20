Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_case :
  incr_list_spec
    [3.8%R; -2.1%R; 9.406367499891232%R; 3.2%R; 7.9%R; -2.1%R]
    [4.8%R; -1.1%R; 10.406367499891232%R; 4.2%R; 8.9%R; -1.1%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace (3.8%R + 1) with 4.8%R by lra.
  replace (-2.1%R + 1) with (-1.1%R) by lra.
  replace (9.406367499891232%R + 1) with 10.406367499891232%R by lra.
  replace (3.2%R + 1) with 4.2%R by lra.
  replace (7.9%R + 1) with 8.9%R by lra.
  replace (-2.1%R + 1) with (-1.1%R) by lra.
  reflexivity.
Qed.