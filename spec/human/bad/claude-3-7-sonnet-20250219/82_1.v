Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Open Scope Z_scope.

Definition problem_82_pre (s : string) : Prop := True.

Definition problem_82_spec (s : string) (b : bool) : Prop :=
  b = true <-> prime (Z.of_nat (length s)).

Example problem_82_test_hello :
  problem_82_spec "Hello" true.
Proof.
  unfold problem_82_spec.
  split.
  - intro H. rewrite H. simpl.
    (* length "Hello" = 5 *)
    (* Prove prime 5 *)
    (* prime 5 means 1 < 5 and any divisor of 5 is 1 or 5 *)
    unfold prime.
    split.
    + lia.
    + intros d [Hdiv].
      apply Znumtheory.Zdivide_prime_inv in Hdiv; auto.
      lia.
  - intro Hprime.
    (* We want to prove: true = true *)
    reflexivity.
Qed.