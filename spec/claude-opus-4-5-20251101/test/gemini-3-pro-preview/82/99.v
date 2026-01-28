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

Example test_prime_length_new : prime_length_spec "abZabcdabcdegabcdefgeeadefg" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - intro H.
    unfold is_prime in H.
    destruct H as [_ Hforall].
    specialize (Hforall 3).
    assert (H_cond : 2 <= 3 /\ 3 * 3 <= 27).
    { split; lia. }
    destruct H_cond as [H_le H_sq].
    specialize (Hforall H_le H_sq).
    simpl in Hforall.
    exfalso.
    apply Hforall.
    reflexivity.
Qed.