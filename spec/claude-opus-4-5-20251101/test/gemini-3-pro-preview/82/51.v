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

Example test_prime_length_composite : prime_length_spec "abcdefzyxwvutsrqponmledcbaabcddefghi" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate.
  - intro H.
    unfold is_prime in H.
    destruct H as [_ H].
    specialize (H 2).
    assert (2 <= 2) by lia.
    assert (2 * 2 <= 36) by lia.
    specialize (H H0 H1).
    simpl in H.
    contradiction.
Qed.