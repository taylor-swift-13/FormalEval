Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.
Open Scope string_scope.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_radar :
  problem_48_spec "radar" true.
Proof.
  unfold problem_48_spec.
  split.
  - intros _ i Hi.
    simpl in *.
    destruct i as [| [| i]].
    + simpl. reflexivity.
    + simpl. reflexivity.
    + exfalso. lia.
  - intros _. reflexivity.
Qed.