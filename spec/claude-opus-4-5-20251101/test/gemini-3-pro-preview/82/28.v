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

Example test_prime_length_composite : prime_length_spec "abcdefabcddefghi" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H.
    discriminate.
  - unfold is_prime.
    intros [Hge Hforall].
    specialize (Hforall 2).
    assert (H1: 2 <= 2) by lia.
    assert (H2: 2 * 2 <= 16) by lia.
    specialize (Hforall H1 H2).
    simpl in Hforall.
    contradiction.
Qed.