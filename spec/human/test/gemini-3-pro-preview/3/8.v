Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_zeros: problem_3_spec [0; 0; 0; 0] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [H_eq H_lt]]].
    destruct prefix as [|z1 [|z2 [|z3 [|z4 [|z5 tail]]]]];
    inversion H_eq; subst; simpl in H_lt; lia.
  - intros H.
    discriminate H.
Qed.