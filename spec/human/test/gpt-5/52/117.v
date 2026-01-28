Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [10%Z; 20%Z; -30%Z; 40%Z; -50%Z] 14%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    specialize (H 20%Z).
    assert (In 20%Z [10%Z; 20%Z; -30%Z; 40%Z; -50%Z]) as Hin.
    { simpl. right. left. reflexivity. }
    specialize (H Hin).
    assert (~ (20%Z < 14%Z)) by lia.
    contradiction.
  - intros Hfalse.
    intros x HIn.
    exfalso.
    discriminate Hfalse.
Qed.