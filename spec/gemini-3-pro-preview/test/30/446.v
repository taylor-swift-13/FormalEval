Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [0.5; -4; 2.5; 5; -2.2; -8; -4; -7; 9.9; -11.18889279027017; -10.5; 2.5; 9.9] [0.5; 2.5; 5; 9.9; 2.5; 9.9].
Proof.
  unfold get_positive_spec.
  cbv [filter].
  repeat match goal with
  | |- context [if Rgt_dec ?x 0 then _ else _] =>
      destruct (Rgt_dec x 0); [ try (exfalso; lra) | try (exfalso; lra) ]
  end.
  reflexivity.
Qed.