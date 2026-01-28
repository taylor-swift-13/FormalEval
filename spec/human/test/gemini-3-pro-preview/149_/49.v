Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
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

Inductive insert_string_rel : string -> list string -> list string -> Prop :=
| isr_nil : forall s, insert_string_rel s nil [s]
| isr_cons_le : forall s h t, string_le_rel s h -> insert_string_rel s (h :: t) (s :: h :: t)
| isr_cons_gt : forall s h t res, string_le_rel h s -> insert_string_rel s t res -> insert_string_rel s (h :: t) (h :: res).

Inductive sorted_by_string_le_rel : list string -> list string -> Prop :=
| sbslr_nil : sorted_by_string_le_rel nil nil
| sbslr_cons : forall s ss sorted_tail res,
   sorted_by_string_le_rel ss sorted_tail ->
   insert_string_rel s sorted_tail res ->
   sorted_by_string_le_rel (s :: ss) res.

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  exists filtered, filter_even_length_rel input filtered /\
    sorted_by_string_le_rel filtered output.

Example problem_149_test : problem_149_spec ["python"; "java"; "ruby"] ["java"; "ruby"; "python"].
Proof.
  unfold problem_149_spec.
  exists ["python"; "java"; "ruby"].
  split.
  - apply felr_keep.
    + apply helr_build. simpl. reflexivity.
    + apply felr_keep.
      * apply helr_build. simpl. reflexivity.
      * apply felr_keep.
        -- apply helr_build. simpl. reflexivity.
        -- apply felr_nil.
  - apply sbslr_cons with (sorted_tail := ["java"; "ruby"]).
    + apply sbslr_cons with (sorted_tail := ["ruby"]).
      * apply sbslr_cons with (sorted_tail := []).
        -- apply sbslr_nil.
        -- apply isr_nil.
      * apply isr_cons_le.
        apply slr_length_eq.
        -- simpl. reflexivity.
        -- apply llr_lt. simpl. reflexivity.
    + apply isr_cons_gt.
      * apply slr_length_lt. simpl. repeat constructor.
      * apply isr_cons_gt.
        -- apply slr_length_lt. simpl. repeat constructor.
        -- apply isr_nil.
Qed.