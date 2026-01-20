Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_abZabcdabcdegabcdefgeeadefg : prime_length_spec "abZabcdabcdegabcdefgeeadefg" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros H.
    unfold is_prime in H.
    destruct H as [Hge2 Hdiv].
    exfalso.
    assert (H3: 2 <= 3) by lia.
    assert (H3sq: 3 * 3 <= 27) by lia.
    specialize (Hdiv 3 H3 H3sq).
    simpl in Hdiv.
    apply Hdiv.
    reflexivity.
Qed.