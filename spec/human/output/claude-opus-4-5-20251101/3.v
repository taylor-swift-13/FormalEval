Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Lia.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_below_zero_1 : problem_3_spec [] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Happ Hsum]]].
    destruct prefix.
    + simpl in Hsum. lia.
    + simpl in Happ. discriminate.
  - intros H. discriminate.
Qed.