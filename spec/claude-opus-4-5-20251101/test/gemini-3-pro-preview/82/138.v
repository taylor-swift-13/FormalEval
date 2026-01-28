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

Example test_prime_length_dog : prime_length_spec "dog." false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate.
  - unfold is_prime.
    intros [Hge Hcheck].
    specialize (Hcheck 2).
    assert (H_cond1: 2 <= 2) by lia.
    assert (H_cond2: 2 * 2 <= 4) by lia.
    specialize (Hcheck H_cond1 H_cond2).
    simpl in Hcheck.
    exfalso.
    apply Hcheck.
    reflexivity.
Qed.