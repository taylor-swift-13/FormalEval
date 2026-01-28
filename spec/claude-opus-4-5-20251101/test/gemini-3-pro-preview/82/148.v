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

Example test_prime_length_complex : prime_length_spec "The quick brownover fox jumps Wxjmnzover the lazy dog." false.
Proof.
  unfold prime_length_spec.
  assert (Hlen : String.length "The quick brownover fox jumps Wxjmnzover the lazy dog." = 54).
  { reflexivity. }
  rewrite Hlen.
  split.
  - intros H. discriminate H.
  - intros [Hge Hforall].
    exfalso.
    specialize (Hforall 2).
    assert (Hle : 2 <= 2) by lia.
    assert (Hsq : 2 * 2 <= 54) by lia.
    specialize (Hforall Hle Hsq).
    simpl in Hforall.
    apply Hforall.
    reflexivity.
Qed.