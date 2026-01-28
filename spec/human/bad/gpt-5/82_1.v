(* 导入 Coq 标准库，用于字符串和自然数算术 *)
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope nat_scope.

Definition problem_82_pre (s : string) : Prop := True.

Definition problem_82_spec (s : string) (b : bool) : Prop :=
  b = true <-> prime (Z.of_nat (length s)).

(* Helper lemma: characterization of nat factors of 5 *)
Lemma nat_mult_eq_5 : forall m n : nat,
  m * n = 5 -> (m = 1 /\ n = 5) \/ (m = 5 /\ n = 1).
Proof.
  intros m n H.
  destruct m as [|m1].
  - simpl in H; discriminate.
  destruct m1 as [|m2].
  - (* m = 1 *)
    simpl in H. left. split; [reflexivity|assumption].
  destruct m2 as [|m3].
  - (* m = 2 *)
    simpl in H. lia.
  destruct m3 as [|m4].
  - (* m = 3 *)
    simpl in H. lia.
  destruct m4 as [|m5].
  - (* m = 4 *)
    simpl in H. lia.
  destruct m5 as [|m6].
  - (* m = 5 *)
    simpl in H. assert (n = 1) by lia. right. split; [reflexivity|assumption].
  - (* m >= 6 *)
    destruct n as [|n1].
    + simpl in H; discriminate.
    + assert (S (S (S (S (S (S m6))))) * 1 <= S (S (S (S (S (S m6))))) * S n1) as Hle.
      { apply Nat.mul_le_mono_l. lia. }
      rewrite Nat.mul_1_r in Hle. rewrite H in Hle. lia.
Qed.

(* If |z| = 1 then z = 1 or z = -1 *)
Lemma abs_eq_1_cases : forall z : Z, Z.abs z = 1 -> z = 1 \/ z = -1.
Proof.
  intros z Hz.
  destruct z as [|p|p].
  - simpl in Hz. discriminate.
  - simpl in Hz. inversion Hz. left. reflexivity.
  - simpl in Hz. inversion Hz. right. reflexivity.
Qed.

(* Factorization lemma over Z with nonnegative factors equalling 5 *)
Lemma nonneg_factorization_5 :
  forall A B : Z,
    0 <= A -> 0 <= B -> A * B = 5 ->
    (A = 1 /\ B = 5) \/ (A = 5 /\ B = 1).
Proof.
  intros A B HA HB Hmul.
  assert (Z.to_nat (A * B) = Z.to_nat A * Z.to_nat B) as Hnatmul.
  { apply Z2Nat.inj_mul; assumption. }
  rewrite Hmul in Hnatmul.
  simpl in Hnatmul. (* Z.to_nat 5 = 5 *)
  assert (Z.to_nat A * Z.to_nat B = 5)%nat as Heq by exact Hnatmul.
  apply nat_mult_eq_5 in Heq.
  destruct Heq as [(HA1 & HB5) | (HA5 & HB1)].
  - left.
    split.
    + change 1%nat with (Z.to_nat 1) in HA1.
      apply Z2Nat.inj in HA1; try lia.
      exact HA1.
    + change 5%nat with (Z.to_nat 5) in HB5.
      apply Z2Nat.inj in HB5; try lia.
      exact HB5.
  - right.
    split.
    + change 5%nat with (Z.to_nat 5) in HA5.
      apply Z2Nat.inj in HA5; try lia.
      exact HA5.
    + change 1%nat with (Z.to_nat 1) in HB1.
      apply Z2Nat.inj in HB1; try lia.
      exact HB1.
Qed.

(* Prove that 5 is prime in Z *)
Lemma prime_5 : prime 5.
Proof.
  unfold prime.
  split.
  - lia.
  - intros a b Hab.
    (* Turn equality 5 = a*b into |a|*|b| = 5 *)
    assert (Z.abs a * Z.abs b = 5) as Habsprod.
    { rewrite <- Z.abs_mul. rewrite Hab. simpl. reflexivity. }
    assert (0 <= Z.abs a) by apply Z.abs_nonneg.
    assert (0 <= Z.abs b) by apply Z.abs_nonneg.
    pose proof (nonneg_factorization_5 (Z.abs a) (Z.abs b) H H0 Habsprod) as Hfac.
    destruct Hfac as [(Ha1 & Hb5) | (Ha5 & Hb1)].
    + (* |a| = 1 *)
      apply abs_eq_1_cases in Ha1.
      destruct Ha1 as [Ha | Ha].
      * left. exact Ha.
      * right. left. exact Ha.
    + (* |b| = 1 *)
      apply abs_eq_1_cases in Hb1.
      destruct Hb1 as [Hb | Hb].
      * right. right. left. exact Hb.
      * right. right. right. exact Hb.
Qed.

Example problem_82_example_Hello :
  problem_82_spec "Hello" true.
Proof.
  unfold problem_82_spec.
  simpl.
  split; [intros _; change (prime 5); apply prime_5 | intros _; reflexivity].
Qed.