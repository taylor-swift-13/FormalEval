Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith Coq.Strings.String Coq.ZArith.ZArith Coq.micromega.Lia.
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

Example problem_66_test_case_1 :
  problem_66_pre "ABCD" /\ problem_66_spec "ABCD" (Z.to_nat 266%Z).
Proof.
  split.
  - unfold problem_66_pre. exact I.
  - unfold problem_66_spec. simpl.
    apply (sur_upper "A"%char "BCD" 201%nat).
    + apply (iu_build "A"%char 65%nat). simpl. reflexivity. lia. lia.
    + apply (sur_upper "B"%char "CD" 135%nat).
      * apply (iu_build "B"%char 66%nat). simpl. reflexivity. lia. lia.
      * apply (sur_upper "C"%char "D" 68%nat).
        -- apply (iu_build "C"%char 67%nat). simpl. reflexivity. lia. lia.
        -- apply (sur_upper "D"%char "" 0%nat).
           ++ apply (iu_build "D"%char 68%nat). simpl. reflexivity. lia. lia.
           ++ apply sur_nil.
Qed.