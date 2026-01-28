Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Require Import Coq.Sorting.Permutation.

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

Inductive sorted : list string -> Prop :=
| sorted_nil : sorted nil
| sorted_1 : forall s, sorted [s]
| sorted_cons : forall s1 s2 ss, string_le_rel s1 s2 -> sorted (s2 :: ss) -> sorted (s1 :: s2 :: ss).

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  exists filtered, filter_even_length_rel input filtered /\
    Permutation filtered output /\
    sorted output.

Example problem_149_test : problem_149_spec ["poupular"; "lizardpython"; "is"; ""; "popular"] [""; "is"; "poupular"; "lizardpython"].
Proof.
  unfold problem_149_spec.
  exists ["poupular"; "lizardpython"; "is"; ""].
  split.
  - apply felr_keep.
    + apply helr_build. simpl. reflexivity.
    + apply felr_keep.
      * apply helr_build. simpl. reflexivity.
      * apply felr_keep.
        -- apply helr_build. simpl. reflexivity.
        -- apply felr_keep.
           ++ apply helr_build. simpl. reflexivity.
           ++ apply felr_drop.
              ** intro H. inversion H. simpl in *. discriminate.
              ** apply felr_nil.
  - split.
    + apply perm_trans with (l' := ["poupular"; "lizardpython"; ""; "is"]).
      * apply perm_skip. apply perm_skip. apply perm_swap.
      * apply perm_trans with (l' := ["poupular"; ""; "lizardpython"; "is"]).
        -- apply perm_skip. apply perm_swap.
        -- apply perm_trans with (l' := [""; "poupular"; "lizardpython"; "is"]).
           ++ apply perm_swap.
           ++ apply perm_trans with (l' := [""; "poupular"; "is"; "lizardpython"]).
              ** apply perm_skip. apply perm_skip. apply perm_swap.
              ** apply perm_skip. apply perm_swap.
    + apply sorted_cons.
      * apply slr_length_lt. simpl. repeat constructor.
      * apply sorted_cons.
        -- apply slr_length_lt. simpl. repeat constructor.
        -- apply sorted_cons.
           ++ apply slr_length_lt. simpl. repeat constructor.
           ++ apply sorted_1.
Qed.