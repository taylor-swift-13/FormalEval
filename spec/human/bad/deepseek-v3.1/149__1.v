Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
Import ListNotations.

Definition aa : string := "aa".
Definition a : string := "a".
Definition aaa : string := "aaa".

Inductive has_even_length_rel : string -> Prop :=
| helr_build : forall s, Nat.even (String.length s) = true -> has_even_length_rel s.

Inductive lex_le_rel : string -> string -> Prop :=
| llr_nil : forall s2, lex_le_rel EmptyString s2
| llr_lt : forall c1 s1 c2 s2, Ascii.compare c1 c2 = Lt ->
    lex_le_rel (String c1 s1) (String c2 s2)
| llr_eq : forall c s1 s2, lex_le_rel s1 s2 ->
    lex_le_rel (String c s1) (String c s2).

Inductive string_le_rel : string -> string -> Prop :=
| slr_length_lt : forall s1 s2, String.length s1 < String.length s2 -> string_le_rel s1 s2
| slr_length_eq : forall s1 s2, String.length s1 = String.length s2 -> lex_le_rel s1 s2 ->
    string_le_rel s1 s2.

Inductive filter_even_length_rel : list string -> list string -> Prop :=
| felr_nil : filter_even_length_rel nil nil
| felr_keep : forall s ss res, has_even_length_rel s -> filter_even_length_rel ss res ->
    filter_even_length_rel (s :: ss) (s :: res)
| felr_drop : forall s ss res, ~ has_even_length_rel s -> filter_even_length_rel ss res ->
    filter_even_length_rel (s :: ss) res.

Inductive sorted_by_string_le_rel : list string -> list string -> Prop :=
| sbslr_nil : sorted_by_string_le_rel nil nil
| sbslr_single : forall s, sorted_by_string_le_rel (s :: nil) (s :: nil)
| sbslr_cons : forall s ss sorted_tail,
   (sorted_tail = nil \/ exists h t, sorted_tail = h :: t /\ string_le_rel h s) ->
   sorted_by_string_le_rel ss sorted_tail ->
   sorted_by_string_le_rel (s :: ss) (s :: sorted_tail).

(* 任意字符串列表输入均可 *)
Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  exists filtered, filter_even_length_rel input filtered /\
    sorted_by_string_le_rel filtered output.

Lemma length_aa : String.length aa = 2.
Proof. unfold aa; reflexivity. Qed.

Lemma even_2 : Nat.even 2 = true.
Proof. reflexivity. Qed.

Lemma has_even_length_aa : has_even_length_rel aa.
Proof.
  unfold aa.
  apply helr_build.
  simpl.
  apply even_2.
Qed.

Lemma length_a : String.length a = 1.
Proof. unfold a; reflexivity. Qed.

Lemma even_1 : Nat.even 1 = false.
Proof. reflexivity. Qed.

Lemma not_has_even_length_a : ~ has_even_length_rel a.
Proof.
  intro H.
  inversion H.
  unfold a in H0.
  simpl in H0.
  rewrite even_1 in H0.
  discriminate.
Qed.

Lemma length_aaa : String.length aaa = 3.
Proof. unfold aaa; reflexivity. Qed.

Lemma even_3 : Nat.even 3 = false.
Proof. reflexivity. Qed.

Lemma not_has_even_length_aaa : ~ has_even_length_rel aaa.
Proof.
  intro H.
  inversion H.
  unfold aaa in H0.
  simpl in H0.
  rewrite even_3 in H0.
  discriminate.
Qed.

Lemma filter_even_length_rel_example : 
  filter_even_length_rel [aa; a; aaa] [aa].
Proof.
  apply felr_keep.
  - apply has_even_length_aa.
  - apply felr_drop.
    + apply not_has_even_length_a.
    + apply felr_drop.
      * apply not_has_even_length_aaa.
      * apply felr_nil.
Qed.

Lemma lex_le_refl : forall s, lex_le_rel s s.
Proof.
  induction s as [|c s IH].
  - apply llr_nil.
  - apply llr_eq. apply IH.
Qed.

Lemma string_le_refl : forall s, string_le_rel s s.
Proof.
  intro s.
  apply slr_length_eq.
  - reflexivity.
  - apply lex_le_refl.
Qed.

Lemma sorted_by_string_le_rel_example : sorted_by_string_le_rel [aa] [aa].
Proof.
  apply sbslr_single.
Qed.

Example test_case : problem_149_spec [aa; a; aaa] [aa].
Proof.
  unfold problem_149_spec.
  exists [aa].
  split.
  - apply filter_even_length_rel_example.
  - apply sorted_by_string_le_rel_example.
Qed.