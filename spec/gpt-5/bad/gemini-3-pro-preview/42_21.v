Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition incr_list_spec (l : list R) (res : list R) : Prop :=
  res = List.map (fun x => x + 1) l.

Example test_incr_list_reals : incr_list_spec [0.1; 0.3] [1.1; 1.3].
Proof.
  unfold incr_list_spec.
  simpl.
  f_equal.
  - lra.
  - f_equal.
    + lra.
    + reflexivity.
Qed.