Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Import ListNotations.
Open Scope nat_scope.

Fixpoint sum_digits_fueled (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + sum_digits_fueled (n / 10) fuel'
    end
  end.

Definition sum_digits (n : nat) : nat :=
  sum_digits_fueled n n.

Definition problem_94_pre (lst : list nat) : Prop := True.

Definition problem_94_spec (lst : list nat) (output : nat) : Prop :=
  (exists p,
    In p lst /\
    prime (Z.of_nat p) /\
    (forall p', In p' lst -> prime (Z.of_nat p') -> p' <= p) /\
    output = sum_digits p)
  \/
  ((forall x, In x lst -> ~ prime (Z.of_nat x)) /\ output = 0).

Lemma prime_181_aux : forall n : Z, (1 < n)%Z -> (n | 181)%Z -> (n = 1 \/ n = 181)%Z.
Proof.
  intros n Hn Hdiv.
  destruct Hdiv as [k Hk].
  assert (Hkpos: (k > 0)%Z) by lia.
  assert (Hkle: (k <= 181)%Z) by lia.
  assert (Hnle: (n <= 181)%Z) by lia.
  (* 181 is prime - we verify by checking no divisor works *)
  destruct (Z.eq_dec n 181); [right; auto | left].
  destruct (Z.eq_dec k 1); [lia | exfalso].
  (* If n < 181 and k > 1, then n * k = 181 requires specific factorization *)
  (* 181 = 181 * 1, and 181 is prime *)
  assert (H181: (181 = n * k)%Z) by lia.
  (* Check small primes *)
  destruct (Z.eq_dec n 2); [subst; lia | ].
  destruct (Z.eq_dec n 3); [subst; lia | ].
  destruct (Z.eq_dec n 5); [subst; lia | ].
  destruct (Z.eq_dec n 7); [subst; lia | ].
  destruct (Z.eq_dec n 11); [subst; lia | ].
  destruct (Z.eq_dec n 13); [subst; lia | ].
  (* sqrt(181) ~ 13.4, so we only need to check up to 13 *)
  assert (Hsqrt: (n * n <= 181 -> n <= 13)%Z) by lia.
  assert (Hcase: (n * n <= 181 \/ n * n > 181)%Z) by lia.
  destruct Hcase.
  - assert (n <= 13)%Z by lia.
    (* n is between 2 and 13, not equal to 2,3,5,7,11,13 *)
    destruct (Z.eq_dec n 4); [subst; lia | ].
    destruct (Z.eq_dec n 6); [subst; lia | ].
    destruct (Z.eq_dec n 8); [subst; lia | ].
    destruct (Z.eq_dec n 9); [subst; lia | ].
    destruct (Z.eq_dec n 10); [subst; lia | ].
    destruct (Z.eq_dec n 12); [subst; lia | ].
    lia.
  - (* n * n > 181 means k < n, and k >= 2 *)
    assert (k < n)%Z by nia.
    assert (k >= 2)%Z by lia.
    (* k is a smaller divisor, check it *)
    destruct (Z.eq_dec k 2); [subst; lia | ].
    destruct (Z.eq_dec k 3); [subst; lia | ].
    destruct (Z.eq_dec k 4); [subst; lia | ].
    destruct (Z.eq_dec k 5); [subst; lia | ].
    destruct (Z.eq_dec k 6); [subst; lia | ].
    destruct (Z.eq_dec k 7); [subst; lia | ].
    destruct (Z.eq_dec k 8); [subst; lia | ].
    destruct (Z.eq_dec k 9); [subst; lia | ].
    destruct (Z.eq_dec k 10); [subst; lia | ].
    destruct (Z.eq_dec k 11); [subst; lia | ].
    destruct (Z.eq_dec k 12); [subst; lia | ].
    destruct (Z.eq_dec k 13); [subst; lia | ].
    nia.
Qed.

Lemma prime_181 : prime 181.
Proof.
  constructor.
  - lia.
  - intros n Hn Hdiv.
    apply prime_181_aux; auto.
Qed.

Lemma sum_digits_181 : sum_digits 181 = 10.
Proof.
  reflexivity.
Qed.

Lemma not_prime_0 : ~ prime 0.
Proof.
  intro H. inversion H. lia.
Qed.

Lemma not_prime_1 : ~ prime 1.
Proof.
  intro H. inversion H. lia.
Qed.

Lemma not_prime_4 : ~ prime 4.
Proof.
  intro H. inversion H.
  assert ((2 | 4)%Z) by (exists 2%Z; lia).
  specialize (H1 2%Z ltac:(lia) H2).
  lia.
Qed.

Lemma not_prime_32 : ~ prime 32.
Proof.
  intro H. inversion H.
  assert ((2 | 32)%Z) by (exists 16%Z; lia).
  specialize (H1 2%Z ltac:(lia) H2).
  lia.
Qed.

Lemma not_prime_324 : ~ prime 324.
Proof.
  intro H. inversion H.
  assert ((2 | 324)%Z) by (exists 162%Z; lia).
  specialize (H1 2%Z ltac:(lia) H2).
  lia.
Qed.

Definition test_list := [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3].

Lemma In_181_test_list : In 181 test_list.
Proof.
  unfold test_list. simpl.
  right. right. right. right. right. right. right. right. right. right. right. right. left. reflexivity.
Qed.

Lemma max_prime_181 : forall p', In p' test_list -> prime (Z.of_nat p') -> p' <= 181.
Proof.
  intros p' Hin Hprime.
  unfold test_list in Hin.
  simpl in Hin.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  | H : ?x = ?y |- _ => subst
  end;
  try lia;
  try (exfalso; simpl in Hprime; apply not_prime_0; exact Hprime);
  try (exfalso; simpl in Hprime; apply not_prime_1; exact Hprime);
  try (exfalso; simpl in Hprime; apply not_prime_4; exact Hprime);
  try (exfalso; simpl in Hprime; apply not_prime_32; exact Hprime);
  try (exfalso; simpl in Hprime; apply not_prime_324; exact Hprime).
Qed.

Example problem_94_example :
  problem_94_spec [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3] 10.
Proof.
  unfold problem_94_spec.
  left.
  exists 181.
  split; [| split; [| split]].
  - apply In_181_test_list.
  - exact prime_181.
  - apply max_prime_181.
  - reflexivity.
Qed.