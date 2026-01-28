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

Example test_problem_66 : problem_66_spec "UPPER" 396.
Proof.
  unfold problem_66_spec.
  (* U *)
  replace 396 with (nat_of_ascii "U"%char + 311) by (cbv; reflexivity).
  apply sur_upper.
  { eapply iu_build. reflexivity. cbv. repeat constructor. cbv. repeat constructor. }
  (* P *)
  replace 311 with (nat_of_ascii "P"%char + 231) by (cbv; reflexivity).
  apply sur_upper.
  { eapply iu_build. reflexivity. cbv. repeat constructor. cbv. repeat constructor. }
  (* P *)
  replace 231 with (nat_of_ascii "P"%char + 151) by (cbv; reflexivity).
  apply sur_upper.
  { eapply iu_build. reflexivity. cbv. repeat constructor. cbv. repeat constructor. }
  (* E *)
  replace 151 with (nat_of_ascii "E"%char + 82) by (cbv; reflexivity).
  apply sur_upper.
  { eapply iu_build. reflexivity. cbv. repeat constructor. cbv. repeat constructor. }
  (* R *)
  replace 82 with (nat_of_ascii "R"%char + 0) by (cbv; reflexivity).
  apply sur_upper.
  { eapply iu_build. reflexivity. cbv. repeat constructor. cbv. repeat constructor. }
  (* End *)
  apply sur_nil.
Qed.