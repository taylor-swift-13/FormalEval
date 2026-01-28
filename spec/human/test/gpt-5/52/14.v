Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [1%Z; 2%Z; 4%Z; 10%Z] 0%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    specialize (H 1%Z).
    assert (In 1%Z [1%Z; 2%Z; 4%Z; 10%Z]) by (simpl; auto).
    apply H in H0.
    assert (0 < 1)%Z by lia.
    lia.
  - intros H.
    intros x HIn.
    exfalso.
    discriminate H.
Qed.