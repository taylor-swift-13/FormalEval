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

Example test_prime_length_abcddefghi : prime_length_spec "abcddefghi" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - intro H.
    unfold is_prime in H.
    destruct H as [_ H_forall].
    assert (H_not_div_2: 10 mod 2 <> 0).
    {
      apply H_forall.
      - lia.
      - lia.
    }
    simpl in H_not_div_2.
    contradiction.
Qed.