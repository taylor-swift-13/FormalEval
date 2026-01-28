Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat Coq.Sorting.Permutation.
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

Inductive is_sorted_string_le : list string -> Prop :=
| iss_nil : is_sorted_string_le nil
| iss_single : forall s, is_sorted_string_le (s :: nil)
| iss_cons : forall s1 s2 rest, string_le_rel s1 s2 -> is_sorted_string_le (s2 :: rest) -> is_sorted_string_le (s1 :: s2 :: rest).

Inductive sorted_by_string_le_rel : list string -> list string -> Prop :=
| sbslr_perm_sorted : forall input output, Permutation input output -> is_sorted_string_le output -> sorted_by_string_le_rel input output.

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  exists filtered, filter_even_length_rel input filtered /\
    sorted_by_string_le_rel filtered output.

Example problem_149_test_1 : problem_149_spec ["aaaa"%string; "bbbb"%string; "dd"%string; "cc"%string] ["cc"%string; "dd"%string; "aaaa"%string; "bbbb"%string].
Proof.
  unfold problem_149_spec.
  exists ["aaaa"%string; "bbbb"%string; "dd"%string; "cc"%string].
  split.
  - apply felr_keep.
    + constructor. simpl. reflexivity.
    + apply felr_keep.
      * constructor. simpl. reflexivity.
      * apply felr_keep.
        -- constructor. simpl. reflexivity.
        -- apply felr_keep.
           ++ constructor. simpl. reflexivity.
           ++ apply felr_nil.
  - apply sbslr_perm_sorted.
    + apply Permutation_trans with (l' := ["aaaa"%string; "bbbb"%string; "cc"%string; "dd"%string]).
      * apply perm_skip. apply perm_skip. apply perm_swap.
      * apply Permutation_trans with (l' := ["aaaa"%string; "cc"%string; "bbbb"%string; "dd"%string]).
        -- apply perm_skip. apply perm_swap.
        -- apply Permutation_trans with (l' := ["cc"%string; "aaaa"%string; "bbbb"%string; "dd"%string]).
           ++ apply perm_swap.
           ++ apply Permutation_trans with (l' := ["cc"%string; "aaaa"%string; "dd"%string; "bbbb"%string]).
              ** apply perm_skip. apply perm_skip. apply perm_swap.
              ** apply perm_skip. apply perm_swap.
    + apply iss_cons.
      * apply slr_length_eq. simpl. reflexivity.
        apply llr_lt with (c1 := "c"%char) (s1 := "c"%string) (c2 := "d"%char) (s2 := "d"%string). simpl. reflexivity.
      * apply iss_cons.
        -- apply slr_length_lt. simpl.
           apply Nat.lt_trans with (m := 3).
           ++ apply Nat.lt_succ_diag_r.
           ++ apply Nat.lt_succ_diag_r.
        -- apply iss_cons.
           ++ apply slr_length_eq. simpl. reflexivity.
              apply llr_lt with (c1 := "a"%char) (s1 := "aaa"%string) (c2 := "b"%char) (s2 := "bbb"%string). simpl. reflexivity.
           ++ apply iss_single.
Qed.