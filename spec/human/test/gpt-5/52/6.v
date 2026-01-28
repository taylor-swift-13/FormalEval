Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [1%Z; 8%Z; 4%Z; 10%Z] 10%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (In 10%Z [1%Z; 8%Z; 4%Z; 10%Z]) as Hin.
    { simpl. right. simpl. right. simpl. right. simpl. left. reflexivity. }
    specialize (H 10%Z Hin).
    apply (Z.lt_irrefl 10%Z) in H.
    contradiction.
  - intros H.
    exfalso.
    discriminate H.
Qed.