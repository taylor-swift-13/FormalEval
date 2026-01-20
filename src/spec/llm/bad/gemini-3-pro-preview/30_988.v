Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec [-1.3426789806479305; 32.97170491287429; -2.25; 32.97170491287429] [32.97170491287429; 32.97170491287429].
Proof.
  unfold get_positive_spec.
  repeat (simpl; match goal with
                 | |- context [Rgt_dec ?x 0] => destruct (Rgt_dec x 0); try lra
                 end).
  reflexivity.
Qed.