Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Import ListNotations.
Open Scope Q_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => (0 <? Qnum x)%Z) l.

Example test_get_positive : get_positive_spec 
  [0#1; 77#10; -15#10; 7#1; -75#100; -225#100; -1#1; -2#1; -4#1; -5#1; -3#1; -225#100; 0#1; -75#100] 
  [77#10; 7#1].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.