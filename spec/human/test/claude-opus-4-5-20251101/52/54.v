Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_below_threshold_2 : problem_52_spec [-4%Z; -3%Z; -2%Z; 4%Z] (-1%Z) false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    assert (Hx : In 4%Z [-4%Z; -3%Z; -2%Z; 4%Z]).
    { simpl. right. right. right. left. reflexivity. }
    specialize (H 4%Z Hx).
    lia.
  - intros H. discriminate.
Qed.