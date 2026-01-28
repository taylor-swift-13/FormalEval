Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [99%Z; 100%Z; 28%Z; -50%Z; 20%Z; -10%Z; 28%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Heq Hlt]]].
    repeat (
      destruct prefix;
      [ simpl in Hlt; lia
      | match goal with 
        | H: _ ++ _ = _ :: _ |- _ => inversion H; subst; clear H 
        | H: _ ++ _ = [] |- _ => inversion H
        end ]
    ).
  - intros H. discriminate H.
Qed.