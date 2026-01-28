Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec 
  [0.5; 0; -4; 2.5; 5; -2.2; -8; 7.7; 9.9; -10.5; 9.9] 
  [0.5; 2.5; 5; 7.7; 9.9; 9.9].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
  | |- context [if Rgt_dec ?x ?y then _ else _] =>
      destruct (Rgt_dec x y); try (exfalso; lra)
  end.
  reflexivity.
Qed.