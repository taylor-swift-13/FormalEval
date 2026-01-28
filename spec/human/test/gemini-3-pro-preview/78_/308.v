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

Definition is_prime_hex_bool (c : ascii) : bool :=
  match c with
  | "2"%char => true
  | "3"%char => true
  | "5"%char => true
  | "7"%char => true
  | "B"%char => true
  | "D"%char => true
  | _ => false
  end.

Lemma is_prime_hex_bool_true : forall c, is_prime_hex_bool c = true -> is_prime_hex_digit c.
Proof.
  intros c.
  destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl; intros; try discriminate; constructor.
Qed.

Lemma is_prime_hex_bool_false : forall c, is_prime_hex_bool c = false -> ~ is_prime_hex_digit c.
Proof.
  intros c H Hc.
  inversion Hc; subst; simpl in H; discriminate.
Qed.

Fixpoint count_prime_hex_func (s : string) : nat :=
  match s with
  | "" => 0
  | String c s' =>
      (if is_prime_hex_bool c then 1 else 0) + count_prime_hex_func s'
  end.

Lemma count_prime_hex_correct : forall s, count_prime_hex_rel s (count_prime_hex_func s).
Proof.
  induction s as [|c s IH].
  - simpl. constructor.
  - simpl. destruct (is_prime_hex_bool c) eqn:H.
    + replace (1 + count_prime_hex_func s) with (S (count_prime_hex_func s)) by reflexivity.
      constructor.
      * apply is_prime_hex_bool_true; assumption.
      * assumption.
    + simpl. constructor.
      * apply is_prime_hex_bool_false; assumption.
      * assumption.
Qed.

Example test_case_1 : problem_78_spec "7ABCDEF20202011ACD2020DDBB123ACDF12345B67C2022EEEFAD890AB123ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BBAA2020015E753BD9CEFF23BCCBBD4DEF12345BBBBAACBAABBBBB33773A11DDBC535553BD" 112.
Proof.
  unfold problem_78_spec.
  replace 112 with (count_prime_hex_func "7ABCDEF20202011ACD2020DDBB123ACDF12345B67C2022EEEFAD890AB123ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BBAA2020015E753BD9CEFF23BCCBBD4DEF12345BBBBAACBAABBBBB33773A11DDBC535553BD") by reflexivity.
  apply count_prime_hex_correct.
Qed.