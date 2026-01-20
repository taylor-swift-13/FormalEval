Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Import ListNotations.
Open Scope Q_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => (Qnum x >? 0)%Z) l.

Example test_get_positive : get_positive_spec [0#1; -5#4; -3#2; -9#4; -2#1; -3#1; -5#1; -6#1; -3#1] [].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.