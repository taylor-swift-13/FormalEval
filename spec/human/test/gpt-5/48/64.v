Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_aaaabca :
  problem_48_spec "aaaabca"%string false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    exfalso.
    assert (Hlt : (1 < String.length "aaaabca"%string / 2)%nat) by (vm_compute; lia).
    specialize (H 1 Hlt).
    vm_compute in H.
    discriminate H.
Qed.