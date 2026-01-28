Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.

Open Scope Q_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => negb (Qle_bool x 0)) l.

Example test_get_positive : get_positive_spec [0#1; -5#4; -3#2; -9#4; -2#1; -3#1; -5#1; -6#1] [].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.