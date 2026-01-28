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

Example test_prime_length_long : prime_length_spec "apabacdabcdefgadefgZbcdefzyxwvutsrqponmledcbaabcddefgfhi" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros [Hge Hdiv].
    specialize (Hdiv 2).
    assert (H1 : 2 <= 2) by lia.
    assert (H2 : 2 * 2 <= 56) by lia.
    specialize (Hdiv H1 H2).
    exfalso.
    apply Hdiv.
    reflexivity.
Qed.