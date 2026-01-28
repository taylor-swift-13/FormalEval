Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [100%Z; 2000000%Z; 300%Z; -400%Z; 500%Z; -600%Z] (-1%Z) false.
Proof.
  unfold problem_52_spec.
  split.
  - intros HAll.
    assert (Hlt : 100%Z < -1%Z) by (apply HAll; simpl; left; reflexivity).
    assert (Hcontra : ~(100%Z < -1%Z)) by lia.
    exfalso. apply Hcontra in Hlt. exact Hlt.
  - intros Hfalse. intros x HIn. exfalso. discriminate Hfalse.
Qed.