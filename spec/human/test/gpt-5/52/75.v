Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [-2%Z; -4%Z] (-5%Z) false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H. exfalso.
    specialize (H (-2%Z)).
    assert (HIn: In (-2%Z) [-2%Z; -4%Z]).
    { simpl. left. reflexivity. }
    specialize (H HIn).
    assert (Hcontra: ~ (-2%Z < -5%Z)) by lia.
    apply Hcontra in H.
    exact H.
  - intros HfalseTrue. intros x HIn.
    exfalso. discriminate HfalseTrue.
Qed.