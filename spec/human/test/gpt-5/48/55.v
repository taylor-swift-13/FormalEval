Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_rr :
  problem_48_spec "rr" true.
Proof.
  unfold problem_48_spec.
  split.
  - intros _ i Hi.
    simpl in Hi.
    destruct i.
    + simpl. reflexivity.
    + exfalso. lia.
  - intros _. reflexivity.
Qed.