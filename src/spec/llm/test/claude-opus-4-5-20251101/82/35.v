Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_abcddefg : prime_length_spec "abcddefg" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros H.
    unfold is_prime in H.
    destruct H as [_ H].
    specialize (H 2).
    assert (Hd: 2 <= 2) by lia.
    assert (Hdd: 2 * 2 <= 8) by lia.
    specialize (H Hd Hdd).
    simpl in H.
    exfalso.
    apply H.
    reflexivity.
Qed.