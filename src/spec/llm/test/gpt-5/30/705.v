Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.

Open Scope Q_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => match Qcompare 0%Q x with Lt => true | _ => false end) l.

Example get_positive_spec_test :
  get_positive_spec
    [(1 # 2)%Q; 0%Q; (-4)%Q; (-13662203687087855 # 1000000000000000)%Q; (5 # 2)%Q; 5%Q; (-11 # 5)%Q; (-8)%Q; (77 # 10)%Q; (99 # 10)%Q; (-21 # 2)%Q; (99 # 10)%Q; (-13662203687087855 # 1000000000000000)%Q]
    [(1 # 2)%Q; (5 # 2)%Q; 5%Q; (77 # 10)%Q; (99 # 10)%Q; (99 # 10)%Q].
Proof.
  unfold get_positive_spec.
  vm_compute.
  reflexivity.
Qed.