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

Axiom compare_a_A_Lt : Ascii.compare "a"%char "A"%char = Lt.
Axiom compare_u_i_Lt : Ascii.compare "u"%char "i"%char = Lt.

Example problem_149_test_1 : problem_149_spec ["AI"%string; "ai"%string; "au"%string] ["AI"%string; "ai"%string; "au"%string].
Proof.
  unfold problem_149_spec.
  exists ["AI"%string; "ai"%string; "au"%string].
  split.
  - apply felr_keep.
    + constructor. simpl. reflexivity.
    + apply felr_keep.
      * constructor. simpl. reflexivity.
      * apply felr_keep.
        -- constructor. simpl. reflexivity.
        -- apply felr_nil.
  - apply sbslr_cons with (sorted_tail := ["ai"%string; "au"%string]).
    + right. exists "ai"%string. exists ["au"%string]. split.
      * reflexivity.
      * apply slr_length_eq.
        -- simpl. reflexivity.
        -- apply llr_lt. exact compare_a_A_Lt.
    + apply sbslr_cons with (sorted_tail := ["au"%string]).
      * right. exists "au"%string. exists ([]: list string). split.
        -- reflexivity.
        -- apply slr_length_eq.
           ++ simpl. reflexivity.
           ++ apply llr_eq. apply llr_lt. exact compare_u_i_Lt.
      * apply sbslr_single.
Qed.