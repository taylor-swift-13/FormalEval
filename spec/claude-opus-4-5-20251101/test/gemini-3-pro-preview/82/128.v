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

Example test_prime_length_sentence : prime_length_spec "The quick brown fox jumps over the lahaszy dog." true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + lia.
    + intros d Hge2 Hsq.
      assert (d < 7).
      {
        destruct (le_lt_dec 7 d); [|assumption].
        assert (7 * 7 <= d * d) by (apply Nat.mul_le_mono; assumption).
        lia.
      }
      do 7 (destruct d as [|d]; [ try lia; try (simpl; intro; discriminate) | ]).
      lia.
  - intros _.
    reflexivity.
Qed.