Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_below_threshold_2 : problem_52_spec [1%Z; 3%Z; 4%Z] 2%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (H3 : In 3%Z [1%Z; 3%Z; 4%Z]).
    { simpl. right. left. reflexivity. }
    specialize (H 3%Z H3).
    lia.
  - intros H. discriminate.
Qed.