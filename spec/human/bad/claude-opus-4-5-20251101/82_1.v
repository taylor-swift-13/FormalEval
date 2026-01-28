Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Definition problem_82_pre (s : string) : Prop := True.

Definition problem_82_spec (s : string) (b : bool) : Prop :=
  b = true <-> prime (Z.of_nat (length s)).

(* Compute length of "Hello" *)
Lemma hello_length : length "Hello"%string = 5%nat.
Proof.
  reflexivity.
Qed.

(* Prove that 5 is prime in Z *)
Lemma prime_5_Z : prime 5%Z.
Proof.
  apply prime_intro.
  - lia.
  - intros n Hn Hdiv.
    destruct Hdiv as [k Hk].
    assert (H1: 1 <= n < 5)%Z by lia.
    destruct (Z.eq_dec n 1) as [Heq1|Hneq1].
    + left. exact Heq1.
    + right.
      assert (n = 2 \/ n = 3 \/ n = 4)%Z as Hcases by lia.
      destruct Hcases as [H2|[H3|H4]].
      * subst n. lia.
      * subst n. lia.
      * subst n. lia.
Qed.

Example problem_82_example_1 : problem_82_spec "Hello"%string true.
Proof.
  unfold problem_82_spec.
  split.
  - intros _.
    rewrite hello_length.
    simpl.
    exact prime_5_Z.
  - intros _.
    reflexivity.
Qed.