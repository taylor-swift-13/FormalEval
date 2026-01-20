Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1%R) l.

Example incr_list_spec_example :
  incr_list_spec [1.5%R; 3.8%R; -2.1%R; 7.9%R; 3.8%R] [2.5%R; 4.8%R; -1.1%R; 8.9%R; 4.8%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace (1.5%R + 1%R) with 2.5%R by lra.
  replace (3.8%R + 1%R) with 4.8%R by lra.
  replace (-2.1%R + 1%R) with (-1.1%R) by lra.
  replace (7.9%R + 1%R) with 8.9%R by lra.
  replace (3.8%R + 1%R) with 4.8%R by lra.
  reflexivity.
Qed.