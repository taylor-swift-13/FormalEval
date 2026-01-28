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

Example test_prime_length_abcdgdefg : prime_length_spec "abcdgdefg" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - intro H_prime.
    exfalso.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_check].
    specialize (H_check 3).
    assert (2 <= 3) as H_le by lia.
    assert (3 * 3 <= 9) as H_sq by lia.
    specialize (H_check H_le H_sq).
    apply H_check.
    reflexivity.
Qed.