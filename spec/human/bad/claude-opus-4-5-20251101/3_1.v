Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0 <-> output = true).

Example test_empty : problem_3_spec [] false.
Proof.
  unfold problem_3_spec.
  exists [], [].
  split.
  - simpl. reflexivity.
  - split.
    + intro H. 
      destruct H as [Heq Hlt].
      simpl in Hlt.
      lia.
    + intro H. discriminate H.
Qed.