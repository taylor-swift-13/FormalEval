Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Definition test_input : list Z := [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 18%Z; -15%Z; 6%Z; 8%Z; 29%Z; 8%Z; -31%Z; -19%Z; 21%Z; -19%Z; 1%Z; 4%Z].

Example test_case_new: problem_3_spec test_input false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [H1 H2]]].
    unfold test_input in H1.
    repeat match goal with
    | [ H : prefix ++ _ = _ |- _ ] =>
        destruct prefix as [|? prefix];
        [ simpl in H2; lia
        | inversion H; subst; clear H ]
    end.
  - intros H.
    discriminate H.
Qed.