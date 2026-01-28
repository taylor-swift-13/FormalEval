(* 导入 Coq 标准库，用于字符串和自然数算术 *)
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.

Open Scope string_scope.
Open Scope Z_scope.

(* Specification definition *)
Definition problem_82_pre (s : string) : Prop := True.

Definition problem_82_spec (s : string) (b : bool) : Prop :=
  b = true <-> prime (Z.of_nat (length s)).

(* Example proof for test case: input = ["Hello"], output = true *)
Example test_prime_length_Hello :
  problem_82_spec "Hello" true.
Proof.
  unfold problem_82_spec.
  split; intros.
  - simpl in H.
    (* Length of "Hello" is 5 *)
    assert (Z.of_nat (length "Hello") = 5%Z) by reflexivity.
    rewrite H0.
    (* 5 is a prime number *)
    apply prime_5.
  - simpl.
    assert (Z.of_nat (length "Hello") = 5%Z) by reflexivity.
    rewrite H0 in H.
    (* 5 is a prime number, hence b = true *)
    reflexivity.
Qed.

(* Additional lemma about the primality of 5, which is needed here *)
Lemma prime_5 : prime 5.
Proof.
  unfold prime.
  split.
  - lia.
  - intros.
    destruct H as [k Hk].
    assert (k = 1 \/ k = 5) as [|]; lia.
Qed.