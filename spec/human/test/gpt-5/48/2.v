Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.
Local Open Scope string_scope.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_aba :
  problem_48_spec "aba" true.
Proof.
  unfold problem_48_spec.
  split.
  - intros _ i Hi.
    simpl in Hi.
    destruct i as [|i']; [simpl; reflexivity | exfalso; lia].
  - intros _. reflexivity.
Qed.