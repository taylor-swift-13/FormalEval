Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_prime_length_new : prime_length_spec "Thisthat is not prime." false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H.
    discriminate H.
  - intro H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    specialize (H_forall 2).
    assert (H_le : 2 <= 2) by lia.
    assert (H_sq : 2 * 2 <= 22) by lia.
    specialize (H_forall H_le H_sq).
    simpl in H_forall.
    exfalso.
    apply H_forall.
    reflexivity.
Qed.