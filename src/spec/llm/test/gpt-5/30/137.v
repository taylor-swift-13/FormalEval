Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Import ListNotations.

Open Scope Q_scope.
Open Scope Z_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => Z.gtb (Qnum x) 0%Z) l.

Example get_positive_spec_test :
  get_positive_spec
    [(1 # 2)%Q; (-4 # 1)%Q; (5 # 2)%Q; (5 # 1)%Q; (-11 # 5)%Q; (-8 # 1)%Q; (-4 # 1)%Q; (-7 # 1)%Q; (-21 # 2)%Q; (99 # 10)%Q; (-21 # 2)%Q]
    [(1 # 2)%Q; (5 # 2)%Q; (5 # 1)%Q; (99 # 10)%Q].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.