Require Import Nat.
Require Import Lia.
Require Import ZArith.

Open Scope nat_scope.

Definition is_prime_spec (n : nat) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 ->
   (exists i, 2 <= i < n /\ n mod i = 0 -> result = false) /\
   (forall i, 2 <= i < n -> n mod i <> 0 -> result = true)).

Example z_input_6_nat : Z.to_nat 6%Z = 6%nat.
Proof. reflexivity. Qed.

Example mod_6_2 : 6 mod 2 = 0.
Proof. reflexivity. Qed.

Example mod_6_5 : 6 mod 5 = 1.
Proof. reflexivity. Qed.

Example is_prime_spec_6_false_contradiction : ~ is_prime_spec (Z.to_nat 6%Z) false.
Proof.
  rewrite z_input_6_nat.
  unfold is_prime_spec.
  intros [Hle Hgt].
  specialize (Hgt ltac:(lia)) as [Hex Hforall].
  specialize (Hforall 5).
  assert (Hrange: 2 <= 5 < 6) by (split; lia).
  assert (Hmod: 6 mod 5 <> 0) by (simpl; discriminate).
  specialize (Hforall Hrange Hmod).
  discriminate.
Qed.