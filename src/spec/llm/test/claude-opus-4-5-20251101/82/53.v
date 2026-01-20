Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_abcddbefg : prime_length_spec "abcddbefg" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros H.
    unfold is_prime in H.
    destruct H as [_ H].
    specialize (H 3).
    assert (Hcontra: 2 <= 3) by lia.
    assert (Hdd: 3 * 3 <= 9) by lia.
    specialize (H Hcontra Hdd).
    simpl in H.
    exfalso.
    apply H.
    reflexivity.
Qed.