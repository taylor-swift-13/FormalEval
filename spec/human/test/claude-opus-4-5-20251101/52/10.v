Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_below_threshold_2 : problem_52_spec [2%Z; 4%Z; 6%Z; 8%Z] 7%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (H8 : In 8%Z [2%Z; 4%Z; 6%Z; 8%Z]).
    { simpl. right. right. right. left. reflexivity. }
    specialize (H 8%Z H8).
    lia.
  - intros H. discriminate.
Qed.