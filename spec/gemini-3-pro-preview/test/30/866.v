Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec 
  [20.235836471463873%R; -89.04346588476734%R; -2.651030586877352%R; 33.195768044846155%R; 32.97170491287429%R; -2.25%R] 
  [20.235836471463873%R; 33.195768044846155%R; 32.97170491287429%R].
Proof.
  unfold get_positive_spec.
  repeat (simpl; match goal with
    | |- context[if Rgt_dec ?x 0 then _ else _] =>
      destruct (Rgt_dec x 0); [ try (exfalso; lra) | try (exfalso; lra) ]
    end).
  reflexivity.
Qed.