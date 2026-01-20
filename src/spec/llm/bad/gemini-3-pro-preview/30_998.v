Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [0.5; 0; -4; 2.5; 5; -2.2; -8; 7.7; -10.5; -10.338878645170468; -8] [0.5; 2.5; 5; 7.7].
Proof.
  unfold get_positive_spec.
  repeat (
    match goal with
    | |- context [Rgt_dec ?x 0] =>
      destruct (Rgt_dec x 0); [ try lra | try lra ]
    end
  ).
  simpl.
  reflexivity.
Qed.