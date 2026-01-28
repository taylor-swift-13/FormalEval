Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Q_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => Qlt_bool 0 x) l.

Example test_get_positive : get_positive_spec 
  [(-3#1); (1#2); (-4#1); (5#2); (5#1); (-11#5); (-8#1); (-4#1); (-7#1); (-21#2); (99#10); (-21#2); (-4#1)] 
  [(1#2); (5#2); (5#1); (99#10)].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.