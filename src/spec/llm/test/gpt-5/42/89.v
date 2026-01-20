Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example incr_list_spec_decimal :
  incr_list_spec [0.535542569745228%R] [1.535542569745228%R].
Proof.
  unfold incr_list_spec.
  simpl.
  replace (1.535542569745228%R) with (0.535542569745228%R + 1%R) by lra.
  reflexivity.
Qed.