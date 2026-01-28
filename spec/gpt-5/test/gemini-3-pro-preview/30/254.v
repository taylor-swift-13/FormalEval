Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [0; -1.25; -1.5; -0.75; -2.25; -1; -2; -3; -4; -5; -6; 0; 0; -2.25] [].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat (match goal with
          | |- context [Rgt_dec ?x ?y] => 
            destruct (Rgt_dec x y); [ lra | simpl ]
          end).
  reflexivity.
Qed.