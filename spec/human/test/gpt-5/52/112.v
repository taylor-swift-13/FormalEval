Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [1000%Z; 500%Z; 250%Z; 125%Z] 125%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    assert (1000%Z < 125%Z) by (apply H; simpl; left; reflexivity).
    lia.
  - intros Heq.
    intros x HIn.
    discriminate Heq.
Qed.