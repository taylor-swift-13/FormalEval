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

Example test_problem_66 : problem_66_spec "You arE Very Smart" 327.
Proof.
  unfold problem_66_spec.
  repeat match goal with
  | [ |- sum_uppercase_rel "" 0 ] => apply sur_nil
  | [ |- sum_uppercase_rel (String ?c ?s) ?tot ] =>
      (let n_val := eval compute in (nat_of_ascii c) in
       let rem := eval compute in (tot - n_val) in
       replace tot with (n_val + rem) by reflexivity;
       apply sur_upper; [
         econstructor; [ reflexivity | apply Nat.leb_le; reflexivity | apply Nat.leb_le; reflexivity ]
       | ])
      ||
      (apply sur_not_upper; [
         intro H; inversion H; subst; simpl in *;
         repeat match goal with
         | [ H_ineq : _ <= _ |- _ ] => apply Nat.leb_le in H_ineq; try discriminate
         end
       | ])
  end.
Qed.