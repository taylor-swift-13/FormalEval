Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Import ListNotations.

Open Scope Q_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => (Qnum x >? 0)%Z) l.

Example test_get_positive : get_positive_spec 
  [(-3#1); (1#2); (-4#1); (5#2); (5#1); (-22#10); (-8#1); (-4#1); (-7#1); (-21#2); (99#10); (-21#2)] 
  [(1#2); (5#2); (5#1); (99#10)].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.