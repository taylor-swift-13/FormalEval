Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
Import ListNotations.

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

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  exists filtered, filter_even_length_rel input filtered /\
    sorted_by_string_le_rel filtered output.

Definition s_d := String "d"%char EmptyString.
Definition s_dcba := String "d"%char (String "c"%char (String "b"%char (String "a"%char EmptyString))).
Definition s_abcd := String "a"%char (String "b"%char (String "c"%char (String "d"%char EmptyString))).
Definition s_a := String "a"%char EmptyString.

Example test_case_fixed :
  problem_149_spec [s_d; s_dcba; s_abcd; s_a] [s_abcd; s_dcba].
Proof.
  unfold problem_149_spec.
  exists [s_abcd; s_dcba].
  split.

  - (* filter_even_length_rel [s_d; s_dcba; s_abcd; s_a] [s_abcd; s_dcba] *)
    apply felr_drop.
    + unfold not. intros H. inversion H. simpl in H1. discriminate.
    + apply felr_keep.
      * apply helr_build. simpl. reflexivity.
      * apply felr_keep.
        -- apply helr_build. simpl. reflexivity.
        -- apply felr_drop.
           ++ unfold not. intros H. inversion H. simpl in H1. discriminate.
           ++ apply felr_nil.

  - (* sorted_by_string_le_rel [s_abcd; s_dcba] [s_abcd; s_dcba] *)
    apply sbslr_cons with (sorted_tail := [s_dcba]).
    + right. exists s_dcba, nil. split.
      * reflexivity.
      * unfold string_le_rel. apply slr_length_eq.
        -- simpl. reflexivity.
        -- apply llr_lt. simpl. reflexivity.
    + apply sbslr_single.
Qed.