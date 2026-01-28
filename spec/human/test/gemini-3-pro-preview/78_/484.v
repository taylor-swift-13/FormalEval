Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Inductive is_prime_hex_digit : ascii -> Prop :=
| iphd_2 : is_prime_hex_digit "2"%char
| iphd_3 : is_prime_hex_digit "3"%char
| iphd_5 : is_prime_hex_digit "5"%char
| iphd_7 : is_prime_hex_digit "7"%char
| iphd_B : is_prime_hex_digit "B"%char
| iphd_D : is_prime_hex_digit "D"%char.

Inductive count_prime_hex_rel : string -> nat -> Prop :=
| cphr_nil : count_prime_hex_rel "" 0%nat
| cphr_prime : forall h t n, is_prime_hex_digit h -> count_prime_hex_rel t n ->
    count_prime_hex_rel (String h t) (S n)
| cphr_not_prime : forall h t n, ~ is_prime_hex_digit h -> count_prime_hex_rel t n ->
    count_prime_hex_rel (String h t) n.

Definition problem_78_pre (s : string) : Prop := True.

Definition problem_78_spec (s : string) (output : nat) : Prop :=
  count_prime_hex_rel s output.

Definition is_prime_hex_digit_b (c : ascii) : bool :=
  if Ascii.eqb c "2"%char then true
  else if Ascii.eqb c "3"%char then true
  else if Ascii.eqb c "5"%char then true
  else if Ascii.eqb c "7"%char then true
  else if Ascii.eqb c "B"%char then true
  else if Ascii.eqb c "D"%char then true
  else false.

Lemma valid_prime_hex : forall c, is_prime_hex_digit_b c = true -> is_prime_hex_digit c.
Proof.
  intros c H.
  unfold is_prime_hex_digit_b in H.
  destruct (Ascii.eqb c "2"%char) eqn:E2. { apply Ascii.eqb_eq in E2. subst. apply iphd_2. }
  destruct (Ascii.eqb c "3"%char) eqn:E3. { apply Ascii.eqb_eq in E3. subst. apply iphd_3. }
  destruct (Ascii.eqb c "5"%char) eqn:E5. { apply Ascii.eqb_eq in E5. subst. apply iphd_5. }
  destruct (Ascii.eqb c "7"%char) eqn:E7. { apply Ascii.eqb_eq in E7. subst. apply iphd_7. }
  destruct (Ascii.eqb c "B"%char) eqn:EB. { apply Ascii.eqb_eq in EB. subst. apply iphd_B. }
  destruct (Ascii.eqb c "D"%char) eqn:ED. { apply Ascii.eqb_eq in ED. subst. apply iphd_D. }
  discriminate.
Qed.

Lemma invalid_prime_hex : forall c, is_prime_hex_digit_b c = false -> ~ is_prime_hex_digit c.
Proof.
  intros c H contra.
  inversion contra; subst;
  unfold is_prime_hex_digit_b in H; simpl in H; discriminate.
Qed.

Fixpoint count_prime_hex_f (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
      if is_prime_hex_digit_b c then S (count_prime_hex_f s') else count_prime_hex_f s'
  end.

Lemma count_prime_hex_f_correct : forall s, count_prime_hex_rel s (count_prime_hex_f s).
Proof.
  induction s.
  - simpl. apply cphr_nil.
  - simpl. destruct (is_prime_hex_digit_b a) eqn:E.
    + apply cphr_prime.
      * apply valid_prime_hex; assumption.
      * assumption.
    + apply cphr_not_prime.
      * apply invalid_prime_hex; assumption.
      * assumption.
Qed.

Example test_case_1 : problem_78_spec "11ABCD22020DDBB12345B67C2022EEEFAD890ABAB4CDEF202020CBAABBBDDDDDDCCCCC111112345B67C1BB333AB4CDEF202020CBAABBB5DDDDDDCCCCC111112212345B67CEEFAD890ABCDEF12345BB5AA2020033CEEEF753BDCEEFAD2020123456789ABCDEABCDEF202020CBAABBBDDDDDDCCCCC1111122222333334444455555F0EAED44444555555A113DDBC2001221234275322022EBDCEEFFBA7F89ABCDEF0025B67CEEFAD890ABCDEF12345BBAA2020033444555555CDEF12345BBBBAA" 184.
Proof.
  unfold problem_78_spec.
  apply count_prime_hex_f_correct.
Qed.