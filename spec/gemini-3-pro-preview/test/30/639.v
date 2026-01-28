Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [9.9; 0.5; -2.25] [9.9; 0.5].
Proof.
  unfold get_positive_spec.
  simpl.
  destruct (Rgt_dec 9.9 0); try lra.
  destruct (Rgt_dec 0.5 0); try lra.
  destruct (Rgt_dec (-2.25) 0); try lra.
  reflexivity.
Qed.