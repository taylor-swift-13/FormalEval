Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.PArith.PArith.
Import ListNotations.

Open Scope Z_scope.
Open Scope positive_scope.

Definition get_positive_spec (l : list Q) (res : list Q) : Prop :=
  res = filter (fun x => Z.gtb (Qnum x) 0%Z) l.

Example get_positive_spec_test :
  get_positive_spec
    [
      Qmake 1%Z 2%positive;
      inject_Z 0%Z;
      Qmake 10538283343362641%Z 1000000000000000%positive;
      Qmake 2493175152910768%Z 100000000000000%positive;
      inject_Z (-4)%Z;
      Qmake 5%Z 2%positive;
      inject_Z 5%Z;
      Qmake (-11)%Z 5%positive;
      Qmake (-2651030586877352)%Z 1000000000000000%positive;
      inject_Z (-8)%Z;
      Qmake 77%Z 10%positive;
      Qmake 99%Z 10%positive;
      Qmake (-21)%Z 2%positive;
      Qmake 99%Z 10%positive;
      inject_Z (-8)%Z;
      Qmake 77%Z 10%positive
    ]
    [
      Qmake 1%Z 2%positive;
      Qmake 10538283343362641%Z 1000000000000000%positive;
      Qmake 2493175152910768%Z 100000000000000%positive;
      Qmake 5%Z 2%positive;
      inject_Z 5%Z;
      Qmake 77%Z 10%positive;
      Qmake 99%Z 10%positive;
      Qmake 99%Z 10%positive;
      Qmake 77%Z 10%positive
    ].
Proof.
  unfold get_positive_spec.
  vm_compute.
  reflexivity.
Qed.