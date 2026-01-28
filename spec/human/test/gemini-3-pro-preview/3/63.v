Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case: problem_3_spec [0; 35; 1; 36; 36] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Heq Hlt]]].
    repeat (
      destruct prefix as [|z prefix]; simpl in Hlt; try lia;
      match goal with
      | H: _ ++ _ = _ |- _ => inversion H; subst; clear H
      end
    ).
  - intros H.
    discriminate H.
Qed.