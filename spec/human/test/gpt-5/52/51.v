Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [7%Z; -2%Z; -3%Z; -3%Z; -4%Z] 0%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros HAll.
    assert (7 < 0) by (apply HAll; simpl; left; reflexivity).
    exfalso.
    lia.
  - intros HFalse.
    intros x HIn.
    exfalso.
    discriminate HFalse.
Qed.