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

Example test_prime_length_false : prime_length_spec "LfgdoOsvaababcdeabcdddefgfgcdefgbcdeaabcdeaebcddefabacdabcdefgeadefggfgbcabcdeabc" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    specialize (H_forall 9).
    assert (2 <= 9) as H_ge by lia.
    assert (9 * 9 <= 81) as H_sq by lia.
    specialize (H_forall H_ge H_sq).
    exfalso.
    apply H_forall.
    reflexivity.
Qed.