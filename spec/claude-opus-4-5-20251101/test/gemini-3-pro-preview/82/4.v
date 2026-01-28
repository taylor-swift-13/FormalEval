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

Example test_prime_length_orange : prime_length_spec "orange" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate.
  - unfold is_prime.
    intros [Hge Hdiv].
    specialize (Hdiv 2).
    assert (2 <= 2) as Hle by lia.
    assert (2 * 2 <= 6) as Hsq by lia.
    specialize (Hdiv Hle Hsq).
    simpl in Hdiv.
    exfalso.
    apply Hdiv.
    reflexivity.
Qed.