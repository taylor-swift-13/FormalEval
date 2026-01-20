Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [10.791699079028088; 25.221353337136023; 25.376288083829433; -3.1836537136945844; -2.6958053769612267; -1.5] [10.791699079028088; 25.221353337136023; 25.376288083829433].
Proof.
  unfold get_positive_spec.
  cbv [filter].
  repeat (match goal with
  | [ |- context[Rgt_dec ?x 0] ] =>
      destruct (Rgt_dec x 0); try (exfalso; lra)
  end; simpl).
  reflexivity.
Qed.