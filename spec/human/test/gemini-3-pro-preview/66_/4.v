Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith Coq.Strings.String.
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

Example test_problem_66 : problem_66_spec "helloE" 69.
Proof.
  unfold problem_66_spec.
  apply sur_not_upper.
  { intro H. inversion H. subst. simpl in *.
    repeat (apply le_S_n in H2). inversion H2. }
  apply sur_not_upper.
  { intro H. inversion H. subst. simpl in *.
    repeat (apply le_S_n in H2). inversion H2. }
  apply sur_not_upper.
  { intro H. inversion H. subst. simpl in *.
    repeat (apply le_S_n in H2). inversion H2. }
  apply sur_not_upper.
  { intro H. inversion H. subst. simpl in *.
    repeat (apply le_S_n in H2). inversion H2. }
  apply sur_not_upper.
  { intro H. inversion H. subst. simpl in *.
    repeat (apply le_S_n in H2). inversion H2. }
  replace 69 with (nat_of_ascii "E" + 0) by (simpl; reflexivity).
  apply sur_upper.
  - apply iu_build with (n:=69).
    + reflexivity.
    + repeat constructor.
    + repeat constructor.
  - apply sur_nil.
Qed.