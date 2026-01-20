Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_abcd : prime_length_spec "abcd" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros H.
    unfold is_prime in H.
    destruct H as [H1 H2].
    specialize (H2 2).
    assert (2 <= 2) by lia.
    assert (2 * 2 <= 4) by lia.
    specialize (H2 H H0).
    simpl in H2.
    exfalso.
    apply H2.
    reflexivity.
Qed.