Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_new: problem_3_spec [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 99%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 11%Z; -1%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [H_eq H_lt]]].
    repeat (
      destruct prefix as [|? prefix];
      [ simpl in Hlt; try lia
      | try discriminate H_eq;
        injection H_eq; intros; subst;
        clear H_eq;
        match goal with
        | H : prefix ++ suffix = _ |- _ => rename H into H_eq
        end
      ]
    ).
  - intros H. discriminate H.
Qed.