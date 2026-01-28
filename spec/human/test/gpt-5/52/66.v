Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [-2%Z; -4%Z] (-4%Z) false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    assert (Hin: In (-2%Z) [-2%Z; -4%Z]) by (simpl; left; reflexivity).
    specialize (H (-2%Z) Hin).
    assert (-2%Z >= -4%Z) by lia.
    lia.
  - intros Heq.
    intros x Hin.
    discriminate Heq.
Qed.