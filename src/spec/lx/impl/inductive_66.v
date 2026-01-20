(* HumanEval 66 - Inductive Spec *)
Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.

Inductive is_uppercase : ascii -> Prop :=
| iu_build : forall c n, n = nat_of_ascii c -> 65 <= n -> n <= 90 -> is_uppercase c.

Inductive sum_uppercase_rel : list ascii -> nat -> Prop :=
| sur_nil : sum_uppercase_rel nil 0%nat
| sur_upper : forall c t n, is_uppercase c -> sum_uppercase_rel t n ->
    sum_uppercase_rel (c :: t) (nat_of_ascii c + n)
| sur_not_upper : forall c t n, ~ is_uppercase c -> sum_uppercase_rel t n ->
    sum_uppercase_rel (c :: t) n.

Definition digitSum_spec (l : list ascii) (output : nat) : Prop :=
  sum_uppercase_rel l output.



