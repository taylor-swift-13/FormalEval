Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1%R) l.

Example incr_list_spec_zeros :
  incr_list_spec [0%R; 0%R; 0%R] [1%R; 1%R; 1%R].
Proof.
  unfold incr_list_spec.
  simpl.
  repeat rewrite Rplus_0_l.
  reflexivity.
Qed.