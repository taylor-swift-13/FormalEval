Require Import List.
Require Import String.
Require Import Ascii.
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

Definition problem_7_pre : Prop := True.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  filter_by_substring_impl_rel input sub output.

Lemma app_mid_nonempty_empty :
  forall pre mid suf,
    mid <> EmptyString ->
    pre ++ mid ++ suf <> EmptyString.
Proof.
  intros pre mid suf Hmid.
  destruct pre as [|c pre']; simpl.
  - destruct mid as [|c' mid']; [contradiction|discriminate].
  - discriminate.
Qed.

Lemma empty_not_contains_x : ~ contains_substring_rel EmptyString "x".
Proof.
  intros H.
  inversion H; subst; try discriminate.
  (* We have EmptyString = pre ++ "x" ++ suf *)
  assert (pre ++ "x" ++ suf <> EmptyString) as Hne.
  { apply app_mid_nonempty_empty. discriminate. }
  symmetry in H0.
  apply Hne in H0.
  exact H0.
Qed.

Lemma john_not_contains_x : ~ contains_substring_rel "john" "x".
Proof.
  intros H.
  inversion H; subst; try discriminate.
  (* H0 : "john" = pre ++ "x" ++ suf *)
  destruct pre as [|a pre1]; simpl in H0.
  - inversion H0; discriminate.
  - inversion H0; subst a; clear H0.
    (* H1 : "ohn" = pre1 ++ "x" ++ suf *)
    destruct pre1 as [|a1 pre2]; simpl in H1.
    + inversion H1; discriminate.
    + inversion H1; subst a1; clear H1.
      (* H2 : "hn" = pre2 ++ "x" ++ suf *)
      destruct pre2 as [|a2 pre3]; simpl in H2.
      * inversion H2; discriminate.
      * inversion H2; subst a2; clear H2.
        (* H3 : "n" = pre3 ++ "x" ++ suf *)
        destruct pre3 as [|a3 pre4]; simpl in H3.
        -- inversion H3; discriminate.
        -- inversion H3; subst a3; clear H3.
           (* H4 : EmptyString = pre4 ++ "x" ++ suf *)
           assert (pre4 ++ "x" ++ suf <> EmptyString) as Hne.
           { apply app_mid_nonempty_empty. discriminate. }
           symmetry in H4.
           apply Hne in H4.
           exact H4.
Qed.

Example problem_7_test :
  problem_7_spec [""; "john"] [] "x".
Proof.
  unfold problem_7_spec.
  apply (fbsir_exclude "" ["john"] "x" []).
  - apply empty_not_contains_x.
  - apply (fbsir_exclude "john" [] "x" []).
    + apply john_not_contains_x.
    + apply fbsir_nil.
Qed.