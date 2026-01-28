Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_empty_list : problem_3_spec [] false.
Proof.
  unfold problem_3_spec.
  split.
  - intro H.
    destruct H as [prefix [suffix [H_eq H_lt]]].
    simpl in H_eq.
    destruct prefix.
    + simpl in H_lt. lia.
    + discriminate H_eq.
  - intro H.
    discriminate H.
Qed.