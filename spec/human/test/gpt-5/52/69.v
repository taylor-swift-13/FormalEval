Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [1%Z; 3%Z; 4%Z] 2%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    apply False_ind.
    assert (In 3%Z [1%Z; 3%Z; 4%Z]) by (simpl; right; left; reflexivity).
    pose proof (H 3%Z H0) as Hlt.
    assert (~ 3%Z < 2%Z) by lia.
    apply H1 in Hlt.
    exact Hlt.
  - intros H_eq x HIn.
    discriminate H_eq.
Qed.