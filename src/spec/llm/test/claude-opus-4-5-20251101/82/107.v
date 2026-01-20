Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_abZabcdabcdegabcdaefgeeadefg : prime_length_spec "abZabcdabcdegabcdaefgeeadefg" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros H.
    unfold is_prime in H.
    destruct H as [Hge Hdiv].
    specialize (Hdiv 4).
    assert (H1: 2 <= 4) by lia.
    assert (H2: 4 * 4 <= 28) by lia.
    specialize (Hdiv H1 H2).
    simpl in Hdiv.
    exfalso.
    apply Hdiv.
    reflexivity.
Qed.