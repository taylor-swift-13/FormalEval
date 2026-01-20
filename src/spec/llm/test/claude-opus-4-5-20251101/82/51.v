Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_long_string : prime_length_spec "abcdefzyxwvutsrqponmledcbaabcddefghi" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros H.
    unfold is_prime in H.
    destruct H as [_ Hdiv].
    specialize (Hdiv 6).
    assert (Hcontra: 2 <= 6) by lia.
    assert (Hdd: 6 * 6 <= 36) by lia.
    specialize (Hdiv Hcontra Hdd).
    simpl in Hdiv.
    exfalso.
    apply Hdiv.
    reflexivity.
Qed.