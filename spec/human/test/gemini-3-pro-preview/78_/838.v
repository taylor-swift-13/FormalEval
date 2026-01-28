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
  match c with
  | "2"%char | "3"%char | "5"%char | "7"%char | "B"%char | "D"%char => true
  | _ => false
  end.

Lemma is_prime_hex_digit_b_true : forall c, is_prime_hex_digit_b c = true -> is_prime_hex_digit c.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7] H.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl in H; try discriminate; constructor.
Qed.

Lemma is_prime_hex_digit_b_false : forall c, is_prime_hex_digit_b c = false -> ~ is_prime_hex_digit c.
Proof.
  intros c H contra.
  inversion contra; subst; simpl in H; discriminate.
Qed.

Fixpoint count_prime_hex_aux (s : string) : nat :=
  match s with
  | "" => 0
  | String c s' =>
      if is_prime_hex_digit_b c then S (count_prime_hex_aux s') else count_prime_hex_aux s'
  end.

Lemma count_prime_hex_aux_correct : forall s, count_prime_hex_rel s (count_prime_hex_aux s).
Proof.
  induction s.
  - simpl. constructor.
  - simpl. destruct (is_prime_hex_digit_b a) eqn:E.
    + apply cphr_prime.
      * apply is_prime_hex_digit_b_true; auto.
      * apply IHs.
    + apply cphr_not_prime.
      * apply is_prime_hex_digit_b_false; auto.
      * apply IHs.
Qed.

Example test_case_1 : problem_78_spec "1234567890ABCDEF12345BBAA22012345678900ABCDEFEA12345CACE1721234567890ABCDEF12345BBAA22012334567890ABEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1ACDF11118872159CEFFACDF11118B872159CDEFF23BCCBB333A11DDBCBBBD44234567890ABCDEF12345BBAA20200BAA202002E345B7BAAA200ADEADBBAA202002E" 116.
Proof.
  unfold problem_78_spec.
  replace 116 with (count_prime_hex_aux "1234567890ABCDEF12345BBAA22012345678900ABCDEFEA12345CACE1721234567890ABCDEF12345BBAA22012334567890ABEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1ACDF11118872159CEFFACDF11118B872159CDEFF23BCCBB333A11DDBCBBBD44234567890ABCDEF12345BBAA20200BAA202002E345B7BAAA200ADEADBBAA202002E").
  - apply count_prime_hex_aux_correct.
  - reflexivity.
Qed.