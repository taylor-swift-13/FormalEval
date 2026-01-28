Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [10000000%Z; 9000000%Z; 8000001%Z; 8000000%Z; 7000000%Z; 6000000%Z; 2000000%Z; 7000000%Z] 125%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 10000000%Z).
    assert (HIn : In 10000000%Z [10000000%Z; 9000000%Z; 8000001%Z; 8000000%Z; 7000000%Z; 6000000%Z; 2000000%Z; 7000000%Z]).
    { simpl. left. reflexivity. }
    specialize (H HIn).
    exfalso. lia.
  - intros Hfalse.
    intros x HIn.
    discriminate Hfalse.
Qed.