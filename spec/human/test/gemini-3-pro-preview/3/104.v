Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [0; 6; 0] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Heq Hlt]]].
    destruct prefix as [|x1 [|x2 [|x3 [|x4 rest]]]].
    + simpl in Hlt. lia.
    + inversion Heq; subst. simpl in Hlt. lia.
    + inversion Heq; subst. simpl in Hlt. lia.
    + inversion Heq; subst. simpl in Hlt. lia.
    + inversion Heq.
  - intros H. discriminate H.
Qed.