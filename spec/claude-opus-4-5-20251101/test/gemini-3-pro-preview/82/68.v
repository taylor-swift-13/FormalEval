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

Example test_prime_length_abcdeabcdefgag : prime_length_spec "abcdeabcdefgag" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate H.
  - intros H.
    unfold is_prime in H.
    destruct H as [_ Hforall].
    specialize (Hforall 2).
    assert (Hge : 2 <= 2) by lia.
    assert (Hsq : 2 * 2 <= 14) by lia.
    specialize (Hforall Hge Hsq).
    simpl in Hforall.
    exfalso.
    apply Hforall.
    reflexivity.
Qed.