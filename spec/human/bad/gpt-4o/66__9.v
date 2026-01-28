Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith Coq.Strings.String Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Inductive is_uppercase : ascii -> Prop :=
| iu_build : forall c n, n = Z.of_nat (nat_of_ascii c) -> 65 <= n -> n <= 90 -> is_uppercase c.

Inductive sum_uppercase_rel : string -> Z -> Prop :=
| sur_nil : sum_uppercase_rel "" 0%Z
| sur_upper : forall c t n, is_uppercase c -> sum_uppercase_rel t n ->
    sum_uppercase_rel (String c t) (Z.of_nat (nat_of_ascii c) + n)
| sur_not_upper : forall c t n, ~ is_uppercase c -> sum_uppercase_rel t n ->
    sum_uppercase_rel (String c t) n.

Definition problem_66_pre (s : string) : Prop := True.

Definition problem_66_spec (s : string) (output : Z) : Prop :=
  sum_uppercase_rel s output.

Example test_case_1 : problem_66_spec "123" 0.
Proof.
  apply sur_not_upper.
  - intros H.
    inversion H.
    subst.
    simpl in H1.
    lia.
  - apply sur_not_upper.
    + intros H.
      inversion H.
      subst.
      simpl in H1.
      lia.
    + apply sur_not_upper.
      * intros H.
        inversion H.
        subst.
        simpl in H1.
        lia.
      * apply sur_nil.
Qed.