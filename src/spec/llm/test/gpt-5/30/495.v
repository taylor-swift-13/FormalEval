Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.

Open Scope Q_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => match Qlt_le_dec 0 x with | left _ => true | right _ => false end) l.

Example get_positive_spec_test :
  get_positive_spec [0; 77#10; -3#2; 7; -3#4; -9#4; -1; -2; -4; -5; -3; -9#4; 0; -3#4] [77#10; 7].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.