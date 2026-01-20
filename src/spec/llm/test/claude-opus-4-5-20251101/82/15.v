Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_m : prime_length_spec "M" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    unfold is_prime.
    split.
    + discriminate.
    + intros d Hd Hdd.
      lia.
  - intros H.
    unfold is_prime in H.
    destruct H as [H1 _].
    lia.
Qed.