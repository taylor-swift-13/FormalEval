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

Example test_prime_length_long : prime_length_spec "abrownntidisestablishmentarianism" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate.
  - unfold is_prime.
    intros [_ Hforall].
    assert (H_mod : 33 mod 3 = 0) by reflexivity.
    specialize (Hforall 3).
    assert (H_le : 2 <= 3) by lia.
    assert (H_sq : 3 * 3 <= 33) by lia.
    specialize (Hforall H_le H_sq).
    contradiction.
Qed.