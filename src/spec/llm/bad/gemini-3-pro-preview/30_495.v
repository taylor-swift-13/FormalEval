Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [0; 7.7; -1.5; 7; -0.75; -2.25; -1; -2; -4; -5; -3; -2.25; 0; -0.75] [7.7; 7].
Proof.
  unfold get_positive_spec.
  repeat match goal with
  | [ |- _ = filter _ (?x :: ?tl) ] =>
      destruct (Rgt_dec x 0); [ simpl; try lra | simpl; try lra ]
  end.
  reflexivity.
Qed.