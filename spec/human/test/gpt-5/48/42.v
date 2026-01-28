Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_never_odd_or_e_ven :
  problem_48_spec "never odd or e ven" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate.
  - intros H.
    exfalso.
    specialize (H 3).
    compute in H.
    assert (3 < 9)%nat by lia.
    specialize (H H0).
    compute in H.
    inversion H.
Qed.