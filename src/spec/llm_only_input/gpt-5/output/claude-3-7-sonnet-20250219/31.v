Require Import Nat.
Require Import Bool.
Require Import Lia.
Require Import ZArith.

Definition divides (d n : nat) : Prop :=
  exists k, n = d * k.

Definition is_prime_spec (n : nat) (b : bool) : Prop :=
  b = true <->
    1 < n /\
    (forall d, 1 < d < n -> ~ divides d n).

Example is_prime_spec_6 : is_prime_spec 6 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros [Hlt Hforall].
    exfalso.
    specialize (Hforall 2).
    assert (1 < 2 /\ 2 < 6) by lia.
    specialize (Hforall H).
    apply Hforall.
    unfold divides. exists 3. simpl. reflexivity.
Qed.

Example is_prime_spec_6_Z : is_prime_spec (Z.to_nat 6%Z) false.
Proof.
  simpl. change (is_prime_spec 6 false).
  apply is_prime_spec_6.
Qed.