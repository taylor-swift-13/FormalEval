Require Import Nat.
Require Import Bool.
Require Import Lia.

Definition divides (d n : nat) : Prop :=
  exists k, n = d * k.

Definition is_prime_spec (n : nat) (b : bool) : Prop :=
  b = true <-> 
    1 < n /\
    (forall d, 1 < d < n -> ~ divides d n).

(* Helper function to check if d divides n *)
Definition divides_dec (d n : nat) : bool :=
  match d with
  | 0 => false
  | S _ => Nat.eqb (n mod d) 0
  end.

(* Check if n has any divisor in range [2, k] *)
Fixpoint has_divisor_upto (n k : nat) : bool :=
  match k with
  | 0 => false
  | 1 => false
  | S k' => if divides_dec k n then true else has_divisor_upto n k'
  end.

(* Primality test function *)
Definition is_prime (n : nat) : bool :=
  match n with
  | 0 => false
  | 1 => false
  | S (S _) => negb (has_divisor_upto n (n - 1))
  end.

(* Prove that 2 divides 6 *)
Lemma two_divides_six : divides 2 6.
Proof.
  unfold divides. exists 3. reflexivity.
Qed.

(* Prove that 6 is not prime *)
Lemma six_not_prime : ~ (1 < 6 /\ (forall d, 1 < d < 6 -> ~ divides d 6)).
Proof.
  intros [_ H].
  apply (H 2).
  - lia.
  - exact two_divides_six.
Qed.

Example test_is_prime_6 : is_prime_spec 6 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H. discriminate.
  - intros [H1 H2].
    exfalso.
    apply (H2 2).
    + lia.
    + unfold divides. exists 3. reflexivity.
Qed.