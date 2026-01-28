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

Example test_prime_length_new : prime_length_spec "azyxwvupZtsrqponmlkihgfedcbadeababcdefcddmefegafg" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - unfold is_prime.
    intros [_ Hforall].
    specialize (Hforall 7).
    assert (2 <= 7) by lia.
    assert (7 * 7 <= 49) by lia.
    specialize (Hforall H H0).
    exfalso.
    apply Hforall.
    reflexivity.
Qed.