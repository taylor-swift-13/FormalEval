Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat Coq.Sorting.Permutation.
Import ListNotations.
Open Scope string_scope.

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

Inductive is_sorted_string : list string -> Prop :=
| iss_nil : is_sorted_string nil
| iss_single : forall s, is_sorted_string (s :: nil)
| iss_cons : forall s1 s2 ss, string_le_rel s1 s2 -> is_sorted_string (s2 :: ss) ->
    is_sorted_string (s1 :: s2 :: ss).

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  exists filtered, filter_even_length_rel input filtered /\
    Permutation filtered output /\
    is_sorted_string output.

Example problem_149_test : problem_149_spec ["school"; "AI"; "asdf"; "b"] ["AI"; "asdf"; "school"].
Proof.
  unfold problem_149_spec.
  exists ["school"; "AI"; "asdf"].
  split.
  - apply felr_keep.
    + apply helr_build. simpl. reflexivity.
    + apply felr_keep.
      * apply helr_build. simpl. reflexivity.
      * apply felr_keep.
        -- apply helr_build. simpl. reflexivity.
        -- apply felr_drop.
           ++ intro H. inversion H. simpl in H1. discriminate.
           ++ apply felr_nil.
  - split.
    + apply perm_trans with (l' := "AI" :: "school" :: "asdf" :: nil).
      * apply perm_swap.
      * apply perm_skip. apply perm_swap.
    + apply iss_cons.
      * apply slr_length_lt. simpl. repeat constructor.
      * apply iss_cons.
        -- apply slr_length_lt. simpl. repeat constructor.
        -- apply iss_single.
Qed.