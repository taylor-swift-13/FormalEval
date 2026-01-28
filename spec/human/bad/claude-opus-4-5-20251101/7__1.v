Require Import List.
Require Import String.
Require Import Ascii.
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

Definition problem_7_pre : Prop:= True.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  filter_by_substring_impl_rel input sub output.

(* Helper lemma: string append properties *)
Lemma string_length_append : forall s1 s2 : string,
  String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof.
  induction s1; intros; simpl.
  - reflexivity.
  - rewrite IHs1. reflexivity.
Qed.

Lemma empty_no_nonempty_substring : forall c rest,
  ~ contains_substring_rel EmptyString (String c rest).
Proof.
  intros c rest H.
  inversion H; subst.
  assert (Hlen: String.length EmptyString = String.length (pre ++ String c rest ++ suf)).
  { rewrite H0. reflexivity. }
  simpl in Hlen.
  rewrite string_length_append in Hlen.
  rewrite string_length_append in Hlen.
  simpl in Hlen.
  omega.
Qed.

(* Check if a character appears in a string *)
Fixpoint char_in_string (c : Ascii.ascii) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c' s' => if Ascii.eqb c c' then true else char_in_string c s'
  end.

Lemma char_in_append : forall c s1 s2,
  char_in_string c (s1 ++ s2) = orb (char_in_string c s1) (char_in_string c s2).
Proof.
  induction s1; intros; simpl.
  - reflexivity.
  - destruct (Ascii.eqb c a); simpl; auto.
Qed.

Lemma john_no_x : ~ contains_substring_rel "john" "x".
Proof.
  intro H.
  inversion H; subst.
  (* "john" = pre ++ "x" ++ suf means 'x' appears in "john" *)
  assert (Hx: char_in_string "x"%char "john" = true).
  {
    rewrite H0.
    rewrite char_in_append.
    rewrite char_in_append.
    simpl.
    rewrite Bool.orb_true_r.
    rewrite Bool.orb_true_r.
    reflexivity.
  }
  simpl in Hx.
  discriminate Hx.
Qed.

Example test_filter_by_substring :
  problem_7_spec [EmptyString; "john"] [] "x".
Proof.
  unfold problem_7_spec.
  apply fbsir_exclude.
  - apply empty_no_nonempty_substring.
  - apply fbsir_exclude.
    + apply john_no_x.
    + apply fbsir_nil.
Qed.