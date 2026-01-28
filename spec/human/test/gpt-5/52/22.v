Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [4%Z; -4%Z; 7%Z; 10%Z] 6%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    specialize (H 7%Z).
    assert (In 7%Z [4%Z; -4%Z; 7%Z; 10%Z]) as HIn.
    { simpl. right. right. left. reflexivity. }
    specialize (H HIn).
    assert (6%Z <= 7%Z) by lia.
    apply (Z.lt_irrefl 7%Z).
    apply (Z.lt_le_trans 7%Z 6%Z 7%Z H H0).
  - intros Hfalse.
    intros x HIn.
    exfalso.
    discriminate Hfalse.
Qed.