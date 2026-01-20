Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = map (fun x => x + 1) l.

Example test_incr_list_float : incr_list_spec [2.5] [3.5].
Proof.
  unfold incr_list_spec.
  simpl.
  replace (2.5 + 1) with 3.5 by lra.
  reflexivity.
Qed.