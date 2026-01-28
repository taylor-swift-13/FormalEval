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

Example test_prime_length_dD : prime_length_spec "dD" true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + (* Prove 2 >= 2 *)
      lia.
    + (* Prove forall d, 2 <= d -> d * d <= 2 -> 2 mod d <> 0 *)
      intros d Hge2 Hsq.
      (* Since d >= 2, d * d >= 4, which contradicts d * d <= 2 *)
      assert (2 * 2 <= d * d) as H_lower.
      { apply Nat.mul_le_mono; assumption. }
      lia.
  - intros _.
    reflexivity.
Qed.