Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_zyxwvutsrqponwmlkjihgfedcba : prime_length_spec "zyxwvutsrqponwmlkjihgfedcba" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros H.
    unfold is_prime in H.
    destruct H as [Hge Hdiv].
    exfalso.
    specialize (Hdiv 3).
    assert (H1: 2 <= 3) by lia.
    assert (H2: 3 * 3 <= 27) by lia.
    apply Hdiv in H1.
    + apply H1.
      simpl.
      reflexivity.
    + exact H2.
Qed.