Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [1%Z; 3%Z; 7%Z; 5%Z] (-1)%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros HAll.
    exfalso.
    specialize (HAll 1%Z).
    assert (Hin : In 1%Z [1%Z; 3%Z; 7%Z; 5%Z]) by (simpl; left; reflexivity).
    pose proof (HAll Hin) as Hlt.
    lia.
  - intros HFalseTrue.
    intros x HIn.
    exfalso.
    discriminate HFalseTrue.
Qed.