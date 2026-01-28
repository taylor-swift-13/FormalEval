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

(* Helper functions for proof automation *)
Definition is_prime_hex_digit_bool (c : ascii) : bool :=
  match c with
  | "2"%char | "3"%char | "5"%char | "7"%char | "B"%char | "D"%char => true
  | _ => false
  end.

Lemma is_prime_hex_digit_reflect : forall c,
  if is_prime_hex_digit_bool c then is_prime_hex_digit c else ~ is_prime_hex_digit c.
Proof.
  intros c.
  destruct (is_prime_hex_digit_bool c) eqn:E.
  - destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
    destruct b0, b1, b2, b3, b4, b5, b6, b7; simpl in E; try discriminate;
    try apply iphd_2; try apply iphd_3; try apply iphd_5; try apply iphd_7; try apply iphd_B; try apply iphd_D.
  - intro H. inversion H; subst; simpl in E; discriminate.
Qed.

Fixpoint count_prime_hex_aux (s : string) : nat :=
  match s with
  | "" => 0
  | String c s' =>
      if is_prime_hex_digit_bool c
      then S (count_prime_hex_aux s')
      else count_prime_hex_aux s'
  end.

Lemma count_prime_hex_aux_correct : forall s,
  count_prime_hex_rel s (count_prime_hex_aux s).
Proof.
  induction s as [|c s' IH].
  - apply cphr_nil.
  - simpl. generalize (is_prime_hex_digit_reflect c).
    destruct (is_prime_hex_digit_bool c).
    + intro H. apply cphr_prime; assumption.
    + intro H. apply cphr_not_prime; assumption.
Qed.

Example test_case_1 : problem_78_spec "7773ABB333A11DDBCB75322022EBDCEEFFA7F9ABCDEF0BBB2BB333CA11D0DBC5555A7F89ABCDEF0333A11DDBC5555" 54.
Proof.
  unfold problem_78_spec.
  replace 54 with (count_prime_hex_aux "7773ABB333A11DDBCB75322022EBDCEEFFA7F9ABCDEF0BBB2BB333CA11D0DBC5555A7F89ABCDEF0333A11DDBC5555").
  - apply count_prime_hex_aux_correct.
  - reflexivity.
Qed.