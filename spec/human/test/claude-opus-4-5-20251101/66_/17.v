Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith Coq.Strings.String.
Require Import Lia.
Import ListNotations.
Open Scope string_scope.

Inductive is_uppercase : ascii -> Prop :=
| iu_build : forall c n, n = nat_of_ascii c -> 65 <= n -> n <= 90 -> is_uppercase c.

Inductive sum_uppercase_rel : string -> nat -> Prop :=
| sur_nil : sum_uppercase_rel "" 0%nat
| sur_upper : forall c t n, is_uppercase c -> sum_uppercase_rel t n ->
    sum_uppercase_rel (String c t) (nat_of_ascii c + n)
| sur_not_upper : forall c t n, ~ is_uppercase c -> sum_uppercase_rel t n ->
    sum_uppercase_rel (String c t) n.

Definition problem_66_pre (s : string) : Prop := True.

Definition problem_66_spec (s : string) (output : nat) : Prop :=
  sum_uppercase_rel s output.

Lemma not_uppercase_l : ~ is_uppercase "l"%char.
Proof.
  unfold not. intro H. inversion H. compute in H0. lia.
Qed.

Lemma not_uppercase_o : ~ is_uppercase "o"%char.
Proof.
  unfold not. intro H. inversion H. compute in H0. lia.
Qed.

Lemma not_uppercase_w : ~ is_uppercase "w"%char.
Proof.
  unfold not. intro H. inversion H. compute in H0. lia.
Qed.

Lemma not_uppercase_e : ~ is_uppercase "e"%char.
Proof.
  unfold not. intro H. inversion H. compute in H0. lia.
Qed.

Lemma not_uppercase_r : ~ is_uppercase "r"%char.
Proof.
  unfold not. intro H. inversion H. compute in H0. lia.
Qed.

Lemma not_uppercase_c : ~ is_uppercase "c"%char.
Proof.
  unfold not. intro H. inversion H. compute in H0. lia.
Qed.

Lemma not_uppercase_a : ~ is_uppercase "a"%char.
Proof.
  unfold not. intro H. inversion H. compute in H0. lia.
Qed.

Lemma not_uppercase_s : ~ is_uppercase "s"%char.
Proof.
  unfold not. intro H. inversion H. compute in H0. lia.
Qed.

Example test_case_1 : problem_66_spec "lowercase" 0%nat.
Proof.
  unfold problem_66_spec.
  apply sur_not_upper. exact not_uppercase_l.
  apply sur_not_upper. exact not_uppercase_o.
  apply sur_not_upper. exact not_uppercase_w.
  apply sur_not_upper. exact not_uppercase_e.
  apply sur_not_upper. exact not_uppercase_r.
  apply sur_not_upper. exact not_uppercase_c.
  apply sur_not_upper. exact not_uppercase_a.
  apply sur_not_upper. exact not_uppercase_s.
  apply sur_not_upper. exact not_uppercase_e.
  apply sur_nil.
Qed.