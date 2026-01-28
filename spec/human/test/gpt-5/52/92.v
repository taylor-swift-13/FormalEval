Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [-4%Z; -3%Z; -2%Z; 4%Z] 0%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    assert (In 4%Z [-4%Z; -3%Z; -2%Z; 4%Z]) as HIn.
    { simpl. right. right. right. left. reflexivity. }
    specialize (H 4%Z HIn).
    lia.
  - intros Heq.
    intros x HIn.
    exfalso.
    discriminate Heq.
Qed.