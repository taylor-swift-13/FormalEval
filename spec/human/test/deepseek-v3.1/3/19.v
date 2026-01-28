Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_single_positive : problem_3_spec [1] false.
Proof.
  unfold problem_3_spec.
  split.
  - intro H.
    destruct H as [prefix [suffix [H_eq H_lt]]].
    assert (H_len : length (prefix ++ suffix) = length [1]) by (rewrite H_eq; reflexivity).
    simpl in H_len.
    destruct prefix as [|p ps].
    + simpl in H_lt. lia.
    + destruct ps as [|p' ps'].
      * simpl in H_lt. simpl in H_eq. inversion H_eq. lia.
      * simpl in H_len. lia.
  - intro H.
    discriminate H.
Qed.