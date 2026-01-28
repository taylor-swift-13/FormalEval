Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

(* Precondition definition *)
Definition problem_59_pre (n : Z) : Prop := (Z.gt n 1 /\ ~ (prime n)).

(* Specification definition *)
Definition problem_59_spec (n p: Z) : Prop :=
  prime p /\ (p | n) /\
  (forall q: Z, (prime q /\ (q | n)) -> Z.le q p).

(* Helper function: checks if a number is a factor *)
Definition is_factor (d n: Z) : bool :=
  (n mod d =? 0)%Z.

(* Function to find the largest prime factor *)
Fixpoint largest_prime_factor_impl (n div: Z) : Z :=
  if Z.eqb div n then div
  else if is_factor div n then
    if prime_dec div then largest_prime_factor_impl (n / div) div
    else largest_prime_factor_impl n (Z.succ div)
  else largest_prime_factor_impl n (Z.succ div).

Definition largest_prime_factor (n: Z) : Z :=
  largest_prime_factor_impl n 2.

(* Test case proof *)
Example largest_prime_factor_test_1:
  largest_prime_factor 15 = 5.
Proof.
  unfold largest_prime_factor.
  unfold largest_prime_factor_impl.
  simpl.
  reflexivity.
Qed.

Example largest_prime_factor_test_2:
  problem_59_spec 15 5.
Proof.
  unfold problem_59_spec.
  split.
  - apply prime_5.
  - split.
    + exists 3. simpl. reflexivity.
    + intros q [Hprime [k Hk]].
      destruct (Z_le_gt_dec q 5); auto.
      exfalso.
      assert (q | 15) by (exists k; exact Hk).
      (* Show q is 3 or 5 *)
      assert (q = 3 \/ q = 5) by (apply prime_divisors_exclusive with (n := 15); auto; apply not_prime_15).
      destruct H1 as [H1 | H1]; lia.
Qed.

Close Scope Z_scope.