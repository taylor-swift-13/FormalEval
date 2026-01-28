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

Example test_case_1 : problem_66_spec "abAB" 131%nat.
Proof.
  unfold problem_66_spec.
  apply sur_not_upper.
  - intro H. inversion H. simpl in H0. rewrite H0 in H1. inversion H1. inversion H4. inversion H6. inversion H8. inversion H10. inversion H12. inversion H14. inversion H16. inversion H18. inversion H20. inversion H22. inversion H24. inversion H26. inversion H28. inversion H30. inversion H32. inversion H34. inversion H36. inversion H38. inversion H40. inversion H42. inversion H44. inversion H46. inversion H48. inversion H50. inversion H52. inversion H54. inversion H56. inversion H58. inversion H60. inversion H62.
  - apply sur_not_upper.
    + intro H. inversion H. simpl in H0. rewrite H0 in H1. inversion H1. inversion H4. inversion H6. inversion H8. inversion H10. inversion H12. inversion H14. inversion H16. inversion H18. inversion H20. inversion H22. inversion H24. inversion H26. inversion H28. inversion H30. inversion H32. inversion H34. inversion H36. inversion H38. inversion H40. inversion H42. inversion H44. inversion H46. inversion H48. inversion H50. inversion H52. inversion H54. inversion H56. inversion H58. inversion H60. inversion H62. inversion H64.
    + apply sur_upper.
      * apply (iu_build "A"%char 65). reflexivity. auto. auto.
      * apply sur_upper.
        -- apply (iu_build "B"%char 66). reflexivity. auto. auto.
        -- apply sur_nil.
Qed.