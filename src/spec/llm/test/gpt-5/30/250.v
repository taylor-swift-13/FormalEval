Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.

Open Scope Q_scope.

Definition qgtb (x y : Q) : bool :=
  if Qlt_le_dec y x then true else false.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => qgtb x 0%Q) l.

Example get_positive_spec_test :
  get_positive_spec [0%Q; (-5 # 4)%Q; (-3 # 2)%Q; (-3 # 4)%Q; (-9 # 4)%Q; (-1)%Q; (-2)%Q; (-3)%Q; (-4)%Q; (-5)%Q; (-3)%Q; (-9 # 4)%Q; 0%Q] [].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.