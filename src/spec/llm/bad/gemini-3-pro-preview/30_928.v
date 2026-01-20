Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec 
  [0.5; -1; 24.93175152910768; -4; 2.5; 5; -2.2; -2.651030586877352; -8; 7.7; 9.9; -10.5; -8; 9.9] 
  [0.5; 24.93175152910768; 2.5; 5; 7.7; 9.9; 9.9].
Proof.
  unfold get_positive_spec.
  repeat (simpl; match goal with
                 | |- context [Rgt_dec ?x 0] => destruct (Rgt_dec x 0); [ try lra | try lra ]
                 end).
  reflexivity.
Qed.