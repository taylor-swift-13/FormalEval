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
  intros c H.
  destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl in H; try discriminate;
  try apply iphd_2; try apply iphd_3; try apply iphd_5; try apply iphd_7;
  try apply iphd_B; try apply iphd_D.
Qed.

Lemma is_prime_hex_digit_b_false : forall c, is_prime_hex_digit_b c = false -> ~ is_prime_hex_digit c.
Proof.
  intros c H contra.
  inversion contra; subst; simpl in H; discriminate.
Qed.

Fixpoint count_prime_hex_f (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (if is_prime_hex_digit_b c then 1 else 0) + count_prime_hex_f s'
  end.

Lemma count_prime_hex_rel_correct : forall s, count_prime_hex_rel s (count_prime_hex_f s).
Proof.
  induction s.
  - simpl. apply cphr_nil.
  - simpl.
    remember (is_prime_hex_digit_b a) as check.
    destruct check.
    + apply cphr_prime.
      * apply is_prime_hex_digit_b_true. symmetry. assumption.
      * apply IHs.
    + apply cphr_not_prime.
      * apply is_prime_hex_digit_b_false. symmetry. assumption.
      * apply IHs.
Qed.

Example test_case_1 : problem_78_spec "2ACDF11118872159CEFFACDF11118872159CEFF23BCAC753BDCEEFAD2020121721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BBB3137D1DDBB31CBAA202002E345BBAAA200456789C11ABCD2020DDB1ACDF11118872159CEFF23BCCBBD423456711ABCD2020753BDDDBBBCFFEEDDCCBBAA890ABCDEFA12345BBAA20200BCC22EBB3137D1DDBB31CEFFEEDDCCBBAADEF0EADEA" 137.
Proof.
  unfold problem_78_spec.
  replace 137 with (count_prime_hex_f "2ACDF11118872159CEFFACDF11118872159CEFF23BCAC753BDCEEFAD2020121721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BBB3137D1DDBB31CBAA202002E345BBAAA200456789C11ABCD2020DDB1ACDF11118872159CEFF23BCCBBD423456711ABCD2020753BDDDBBBCFFEEDDCCBBAA890ABCDEFA12345BBAA20200BCC22EBB3137D1DDBB31CEFFEEDDCCBBAADEF0EADEA").
  - apply count_prime_hex_rel_correct.
  - reflexivity.
Qed.