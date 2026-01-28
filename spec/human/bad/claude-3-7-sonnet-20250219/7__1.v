Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.

(* sub 是 s 的子串，当且仅当存在前缀 pre 与后缀 suf 使得 s = pre ++ sub ++ suf。
   约定：空串是任何字符串的子串。 *)
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

Definition problem_7_pre : Prop := True.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  filter_by_substring_impl_rel input sub output.

Example test_case_1 :
  problem_7_spec [EmptyString; "john"] "a" [].
Proof.
  unfold problem_7_spec.
  apply fbsir_exclude.
  - (* ~ contains_substring_rel EmptyString "a" *)
    intros H.
    inversion H.
    + (* csr_empty_any with sub = "a" contradicts *)
      discriminate.
    + (* csr_split: EmptyString = pre ++ "a" ++ suf *)
      subst.
      simpl in *.
      (* "a" non-empty string cannot be part of EmptyString *)
      remember (pre ++ "a" ++ suf) as combined eqn:Heq.
      apply app_inv_head in Heq. destruct Heq as [Heq|Hnil];
      try discriminate.
  - (* filter rest ["john"] "a" [] *)
    apply fbsir_exclude.
    + (* ~ contains_substring_rel "john" "a" *)
      intros H.
      inversion H.
      * (* csr_empty_any with sub = "a" *)
        discriminate.
      * (* csr_split: "john" = pre ++ "a" ++ suf *)
        subst.
        remember "john" as s eqn:Hs.
        assert (forall pre suf, pre ++ "a" ++ suf = s -> False).
        {
          intros pre suf Heq.
          subst s.
          (* Prove by induction on pre that no such split exists *)
          revert suf Heq.
          induction pre as [|c pre' IHp]; intros suf Heq.
          - simpl in Heq.
            destruct "john" eqn:E.
            + simpl in Heq. discriminate.
            + simpl in Heq.
              (* Head chars must match *)
              inversion Heq; subst.
              (* 'a' char does not match head of "john" which is 'j' *)
              discriminate.
          - simpl in Heq.
            destruct "john" eqn:E.
            + simpl in Heq. discriminate.
            + simpl in Heq.
              inversion Heq; subst.
              apply IHp with suf. reflexivity.
        }
        apply H0 with pre suf. reflexivity.
    + (* filter rest [] "a" [] *)
      apply fbsir_nil.
Qed.