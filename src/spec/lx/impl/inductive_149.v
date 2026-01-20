(* HumanEval 149 - Inductive Spec *)
Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Arith.PeanoNat.
Import ListNotations.

Inductive has_even_length_rel : list ascii -> Prop :=
| helr_build : forall s, Nat.even (length s) = true -> has_even_length_rel s.

Inductive lex_le_rel : list ascii -> list ascii -> Prop :=
| llr_nil : forall s2, lex_le_rel nil s2
| llr_lt : forall c1 s1 c2 s2, Ascii.compare c1 c2 = Lt ->
    lex_le_rel (c1 :: s1) (c2 :: s2)
| llr_eq : forall c s1 s2, lex_le_rel s1 s2 ->
    lex_le_rel (c :: s1) (c :: s2).

Inductive string_le_rel : list ascii -> list ascii -> Prop :=
| slr_length_lt : forall s1 s2, length s1 < length s2 -> string_le_rel s1 s2
| slr_length_eq : forall s1 s2, length s1 = length s2 -> lex_le_rel s1 s2 ->
    string_le_rel s1 s2.

Inductive filter_even_length_rel : list (list ascii) -> list (list ascii) -> Prop :=
| felr_nil : filter_even_length_rel nil nil
| felr_keep : forall s ss res, has_even_length_rel s -> filter_even_length_rel ss res ->
    filter_even_length_rel (s :: ss) (s :: res)
| felr_drop : forall s ss res, ~ has_even_length_rel s -> filter_even_length_rel ss res ->
    filter_even_length_rel (s :: ss) res.

Inductive sorted_by_string_le_rel : list (list ascii) -> list (list ascii) -> Prop :=
| sbslr_nil : sorted_by_string_le_rel nil nil
| sbslr_single : forall s, sorted_by_string_le_rel (s :: nil) (s :: nil)
| sbslr_cons : forall s ss sorted_tail,
   (sorted_tail = nil \/ exists h t, sorted_tail = h :: t /\ string_le_rel h s) ->
   sorted_by_string_le_rel ss sorted_tail ->
   sorted_by_string_le_rel (s :: ss) (s :: sorted_tail).

Definition sorted_list_sum_spec (lst_in : list (list ascii)) (lst_out : list (list ascii)) : Prop :=
  exists filtered, filter_even_length_rel lst_in filtered /\
    sorted_by_string_le_rel filtered lst_out.

