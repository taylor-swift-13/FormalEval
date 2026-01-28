Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [3%Z; 1%Z; 4%Z; 7%Z; 10%Z; 7%Z] 6%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    specialize (H 7%Z).
    assert (In 7%Z [3%Z; 1%Z; 4%Z; 7%Z; 10%Z; 7%Z]) as Hin.
    { simpl. right. simpl. right. simpl. right. left. reflexivity. }
    specialize (H Hin).
    lia.
  - intros Heq x HIn.
    exfalso.
    discriminate Heq.
Qed.