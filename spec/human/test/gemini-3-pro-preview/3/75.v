Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [6%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [H_eq H_lt]]].
    destruct prefix as [|x xs].
    + simpl in H_lt. lia.
    + destruct xs as [|y ys].
      * simpl in H_eq. injection H_eq as Hx _. subst x.
        simpl in H_lt. lia.
      * simpl in H_eq. inversion H_eq.
  - intros H. discriminate.
Qed.