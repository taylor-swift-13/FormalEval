Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case: problem_3_spec [1%Z; -1%Z; 1%Z; -1%Z; 30%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -2%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - (* Forward direction: (exists ...) -> false = true *)
    intros [prefix [suffix [Happ Hlt]]].
    repeat (
      destruct prefix as [|x prefix];
      [ simpl in Hlt; lia
      | simpl in Happ; try discriminate; injection Happ as ? Happ; subst ]
    ).
  - (* Backward direction: false = true -> (exists ...) *)
    intros H.
    discriminate H.
Qed.