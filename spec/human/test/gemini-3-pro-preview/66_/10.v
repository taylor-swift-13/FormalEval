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

Example test_problem_66 : problem_66_spec "ABCD" 266.
Proof.
  unfold problem_66_spec.
  apply sur_upper with (n := 201).
  - apply iu_build with (n := 65); [reflexivity | repeat constructor | repeat constructor].
  - apply sur_upper with (n := 135).
    + apply iu_build with (n := 66); [reflexivity | repeat constructor | repeat constructor].
    + apply sur_upper with (n := 68).
      * apply iu_build with (n := 67); [reflexivity | repeat constructor | repeat constructor].
      * apply sur_upper with (n := 0).
        -- apply iu_build with (n := 68); [reflexivity | repeat constructor | repeat constructor].
        -- apply sur_nil.
Qed.