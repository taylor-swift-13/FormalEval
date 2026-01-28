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

Example test_prime_length_complex : prime_length_spec "abcdaabcdgdefgbcdefgadefg" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros Hprime.
    unfold is_prime in Hprime.
    destruct Hprime as [_ Hforall].
    specialize (Hforall 5).
    assert (H_le : 2 <= 5) by lia.
    assert (H_sq : 5 * 5 <= 25) by lia.
    specialize (Hforall H_le H_sq).
    simpl in Hforall.
    contradiction.
Qed.