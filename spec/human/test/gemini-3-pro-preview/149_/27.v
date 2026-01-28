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

Inductive is_sorted : list string -> Prop :=
| is_sorted_nil : is_sorted nil
| is_sorted_single : forall s, is_sorted (s :: nil)
| is_sorted_cons : forall s1 s2 ss, string_le_rel s1 s2 -> is_sorted (s2 :: ss) -> is_sorted (s1 :: s2 :: ss).

Definition sorted_by_string_le_rel (input output : list string) : Prop :=
  Permutation input output /\ is_sorted output.

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  exists filtered, filter_even_length_rel input filtered /\
    sorted_by_string_le_rel filtered output.

Example problem_149_test : problem_149_spec ["popuolar"; "is"; ""; "popular"; "language"] [""; "is"; "language"; "popuolar"].
Proof.
  unfold problem_149_spec.
  exists ["popuolar"; "is"; ""; "language"].
  split.
  - apply felr_keep.
    + apply helr_build. reflexivity.
    + apply felr_keep.
      * apply helr_build. reflexivity.
      * apply felr_keep.
        -- apply helr_build. reflexivity.
        -- apply felr_drop.
           ++ intro H. inversion H. simpl in *. discriminate.
           ++ apply felr_keep.
              ** apply helr_build. reflexivity.
              ** apply felr_nil.
  - unfold sorted_by_string_le_rel. split.
    + apply perm_trans with ("is" :: "popuolar" :: "" :: "language" :: nil).
      * apply perm_swap.
      * apply perm_trans with ("is" :: "" :: "popuolar" :: "language" :: nil).
        -- apply perm_skip. apply perm_swap.
        -- apply perm_trans with ("is" :: "" :: "language" :: "popuolar" :: nil).
           ++ apply perm_skip. apply perm_skip. apply perm_swap.
           ++ apply perm_swap.
    + apply is_sorted_cons.
      * apply slr_length_lt. simpl. repeat constructor.
      * apply is_sorted_cons.
        -- apply slr_length_lt. simpl. repeat constructor.
        -- apply is_sorted_cons.
           ++ apply slr_length_eq.
              ** reflexivity.
              ** simpl. constructor. reflexivity.
           ++ apply is_sorted_single.
Qed.