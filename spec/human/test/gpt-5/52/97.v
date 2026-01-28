Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [3%Z; 1%Z; 1%Z; 4%Z; 7%Z; 10%Z; 7%Z] 6%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    assert (H10 : 10 < 6) by (apply H; simpl; right; right; right; right; right; left; reflexivity).
    lia.
  - intros Heq. intros x HIn.
    exfalso. discriminate Heq.
Qed.