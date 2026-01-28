Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_case :
  problem_48_spec "aaWas it a car or a cat I saw?bWas it a car osteaabcp on no petsrr a ca t I saw?ca" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi. exfalso. discriminate H.
  - intros H.
    exfalso.
    assert (Hlt: (1 < String.length "aaWas it a car or a cat I saw?bWas it a car osteaabcp on no petsrr a ca t I saw?ca" / 2)%nat) by (vm_compute; lia).
    specialize (H 1 Hlt).
    vm_compute in H.
    discriminate H.
Qed.