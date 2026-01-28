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

Example test_prime_length_sentence : prime_length_spec "The quick brown fox jumps over the lazy dog." false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - intro H.
    unfold is_prime in H.
    destruct H as [_ H].
    (* The length is 44, which is divisible by 2. We use this to derive a contradiction. *)
    assert (2 <= 2) by lia.
    assert (2 * 2 <= 44) by lia.
    specialize (H 2 H0 H1).
    simpl in H.
    exfalso.
    apply H.
    reflexivity.
Qed.