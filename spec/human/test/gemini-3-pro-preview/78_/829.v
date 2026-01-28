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

Definition is_prime_hex_digit_bool (c : ascii) : bool :=
  match c with
  | "2"%char => true
  | "3"%char => true
  | "5"%char => true
  | "7"%char => true
  | "B"%char => true
  | "D"%char => true
  | _ => false
  end.

Lemma is_prime_hex_digit_bool_true : forall c, is_prime_hex_digit_bool c = true -> is_prime_hex_digit c.
Proof.
  intros c. destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl; intro H; try discriminate H; constructor.
Qed.

Lemma is_prime_hex_digit_bool_false : forall c, is_prime_hex_digit_bool c = false -> ~ is_prime_hex_digit c.
Proof.
  intros c H Hc. inversion Hc; subst; simpl in H; discriminate.
Qed.

Fixpoint count_prime_hex_func (s : string) : nat :=
  match s with
  | "" => 0
  | String c s' => (if is_prime_hex_digit_bool c then 1 else 0) + count_prime_hex_func s'
  end.

Lemma count_prime_hex_equiv : forall s, count_prime_hex_rel s (count_prime_hex_func s).
Proof.
  induction s.
  - simpl. apply cphr_nil.
  - simpl. destruct (is_prime_hex_digit_bool a) eqn:Heq.
    + replace (1 + count_prime_hex_func s) with (S (count_prime_hex_func s)) by reflexivity.
      apply cphr_prime.
      * apply is_prime_hex_digit_bool_true. assumption.
      * assumption.
    + replace (0 + count_prime_hex_func s) with (count_prime_hex_func s) by reflexivity.
      apply cphr_not_prime.
      * apply is_prime_hex_digit_bool_false. assumption.
      * assumption.
Qed.

Example test_case_1 : problem_78_spec "1234567890ABCDEF12345BBAA22012345678900ABCDEFEA12345CACE1721234567890ABCDEF12345BBAA22012334567890ABCDEFA1234BB37137D1DDBCB1234567890ABCDEF12345BBAA2201234567890ABCDEFA12345BBAA202002EB3133A11DDCBC5BCEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1ACDF11118872159CEFFACDF11118B872159CDEFF23BCCBB333A11DDBCBBBD44234567890ABCDEF12345BBAA20200BAA202002E345B7BAAA200ADEADBBAA202002E" 166.
Proof.
  unfold problem_78_spec.
  assert (H: count_prime_hex_func "1234567890ABCDEF12345BBAA22012345678900ABCDEFEA12345CACE1721234567890ABCDEF12345BBAA22012334567890ABCDEFA1234BB37137D1DDBCB1234567890ABCDEF12345BBAA2201234567890ABCDEFA12345BBAA202002EB3133A11DDCBC5BCEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1ACDF11118872159CEFFACDF11118B872159CDEFF23BCCBB333A11DDBCBBBD44234567890ABCDEF12345BBAA20200BAA202002E345B7BAAA200ADEADBBAA202002E" = 166) by (vm_compute; reflexivity).
  rewrite <- H.
  apply count_prime_hex_equiv.
Qed.