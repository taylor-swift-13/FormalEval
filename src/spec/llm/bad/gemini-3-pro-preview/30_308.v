Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.
Open Scope Q_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => Qlt_bool (0#1) x) l.

Example test_get_positive : get_positive_spec 
  [0#1; 77#10; -3#2; -3#4; -9#4; -1#1; -2#1; -4#1; -5#1; -3#1; -9#4; 0#1; -3#4] 
  [77#10].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.