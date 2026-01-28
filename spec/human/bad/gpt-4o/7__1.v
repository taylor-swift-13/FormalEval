Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.

Inductive contains_substring_rel : string -> string -> Prop :=
  | csr_empty_any : forall s, contains_substring_rel s EmptyString
  | csr_split : forall pre sub suf, contains_substring_rel (pre ++ sub ++ suf) sub.

Inductive filter_by_substring_impl_rel : list string -> string -> list string -> Prop :=
  | fbsir_nil : forall sub, filter_by_substring_impl_rel [] sub []
  | fbsir_include : forall h t sub output,
      contains_substring_rel h sub ->
      filter_by_substring_impl_rel t sub output ->
      filter_by_substring_impl_rel (h :: t) sub (h :: output)
  | fbsir_exclude : forall h t sub output,
      ~ contains_substring_rel h sub ->
      filter_by_substring_impl_rel t sub output ->
      filter_by_substring_impl_rel (h :: t) sub output.

Definition problem_7_pre : Prop:= True.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  filter_by_substring_impl_rel input sub output.

Example test_case_2 : problem_7_spec [""; "john"] [] "a".
Proof.
  apply fbsir_exclude.
  - intro H. inversion H. subst. discriminate.
  - apply fbsir_exclude.
    + intro H. inversion H. subst. discriminate.
    + apply fbsir_nil.
Qed.