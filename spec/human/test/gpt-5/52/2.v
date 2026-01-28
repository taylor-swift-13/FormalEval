Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [1%Z; 20%Z; 4%Z; 10%Z] 5%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    assert (20 < 5).
    { apply H.
      simpl. right. simpl. left. reflexivity. }
    lia.
  - intros H.
    intros x HIn.
    discriminate H.
Qed.