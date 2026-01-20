Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.

Open Scope Q_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => match Qcompare x 0%Q with Gt => true | _ => false end) l.

Example get_positive_spec_test :
  get_positive_spec [1#2; 0#1; 5#2; 5#1; (-11)#5; (-8)#1; (-3)#4; 77#10; 99#10; (-21)#2; 5#1]
                    [1#2; 5#2; 5#1; 77#10; 99#10; 5#1].
Proof.
  unfold get_positive_spec.
  simpl.
  reflexivity.
Qed.