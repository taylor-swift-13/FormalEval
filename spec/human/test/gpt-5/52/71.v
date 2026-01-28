Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_pre (l : list Z) : Prop := True.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [6%Z; 4%Z; -4%Z; 7%Z; 10%Z] 7%Z false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (Hin7 : In 7%Z [6%Z; 4%Z; -4%Z; 7%Z; 10%Z]).
    { simpl. right. right. right. left. reflexivity. }
    specialize (H 7%Z Hin7).
    exfalso. lia.
  - intros H.
    exfalso. discriminate H.
Qed.