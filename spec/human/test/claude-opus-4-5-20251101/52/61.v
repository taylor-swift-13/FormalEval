Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_below_threshold_2 : problem_52_spec [-1%Z; -2%Z; -4%Z] (-5%Z) false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    exfalso.
    assert (Hx : In (-1%Z) [-1%Z; -2%Z; -4%Z]).
    { simpl. left. reflexivity. }
    specialize (H (-1%Z) Hx).
    lia.
  - intros H. discriminate.
Qed.