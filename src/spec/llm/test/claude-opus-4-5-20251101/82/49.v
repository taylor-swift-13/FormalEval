Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_ababcdabcdegabcdefgeadefg : prime_length_spec "ababcdabcdegabcdefgeadefg" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros H.
    unfold is_prime in H.
    destruct H as [_ H].
    specialize (H 5).
    assert (Hd: 2 <= 5) by lia.
    assert (Hdd: 5 * 5 <= 25) by lia.
    specialize (H Hd Hdd).
    simpl in H.
    exfalso.
    apply H.
    reflexivity.
Qed.