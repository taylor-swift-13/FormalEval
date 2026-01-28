Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_case :
  problem_48_spec "ranever oddWas it a car or a sacat I saw? venr" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi.
    exfalso.
    discriminate H.
  - intros Hprop.
    exfalso.
    specialize (Hprop 1%nat).
    assert (Hlt : (1 < String.length "ranever oddWas it a car or a sacat I saw? venr" / 2)%nat) by (simpl; lia).
    specialize (Hprop Hlt).
    simpl in Hprop.
    congruence.
Qed.