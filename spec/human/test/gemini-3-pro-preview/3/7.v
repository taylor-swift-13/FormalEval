Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_0: problem_3_spec [0] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    destruct prefix as [|x rest].
    + simpl in Hlt. lia.
    + destruct rest as [|y rest'].
      * simpl in Happ. injection Happ as Hx. subst x. simpl in Hlt. lia.
      * simpl in Happ. discriminate.
  - intros H. discriminate.
Qed.