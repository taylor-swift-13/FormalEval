Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_aabcdeabcabcdefgfabcddefghibacd : prime_length_spec "aabcdeabcabcdefgfabcddefghibacd" true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + lia.
    + intros d Hd Hdd.
      assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5) by lia.
      destruct H as [H | [H | [H | H]]]; subst d; simpl; discriminate.
  - intros _.
    reflexivity.
Qed.