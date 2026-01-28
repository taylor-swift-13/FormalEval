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

Definition str_aaaa : string := String "a" (String "a" (String "a" (String "a" EmptyString))).
Definition str_bb : string := String "b" (String "b" EmptyString).
Definition str_cccc : string := String "c" (String "c" (String "c" (String "c" EmptyString))).
Definition str_ddd : string := String "d" (String "d" (String "d" EmptyString)).

Inductive is_permutation {A : Type} : list A -> list A -> Prop :=
| perm_nil : is_permutation nil nil
| perm_skip : forall x l1 l2, is_permutation l1 l2 -> is_permutation (x :: l1) (x :: l2)
| perm_swap : forall x y l, is_permutation (x :: y :: l) (y :: x :: l)
| perm_trans : forall l1 l2 l3, is_permutation l1 l2 -> is_permutation l2 l3 -> is_permutation l1 l3.

Inductive sorted_rel : list string -> Prop :=
| sorted_nil : sorted_rel nil
| sorted_one : forall s, sorted_rel (s :: nil)
| sorted_cons : forall s1 s2 t, string_le_rel s1 s2 -> sorted_rel (s2 :: t) -> sorted_rel (s1 :: s2 :: t).

Definition problem_149_spec_v2 (input : list string) (output : list string) : Prop :=
  exists filtered, filter_even_length_rel input filtered /\
    is_permutation filtered output /\ sorted_rel output.

Example test_problem_149 :
  problem_149_spec_v2 (str_aaaa :: str_bb :: str_cccc :: str_ddd :: nil) (str_bb :: str_aaaa :: str_cccc :: nil).
Proof.
  unfold problem_149_spec_v2.
  exists (str_aaaa :: str_bb :: str_cccc :: nil).
  split.
  - apply felr_keep.
    + apply helr_build. unfold str_aaaa. simpl. reflexivity.
    + apply felr_keep.
      * apply helr_build. unfold str_bb. simpl. reflexivity.
      * apply felr_keep.
        -- apply helr_build. unfold str_cccc. simpl. reflexivity.
        -- apply felr_drop.
           ++ unfold not. intro H. inversion H. unfold str_ddd in H0. simpl in H0. discriminate H0.
           ++ apply felr_nil.
  - split.
    + apply perm_swap.
    + apply sorted_cons.
      * apply slr_length_lt. unfold str_bb, str_aaaa. simpl. auto.
      * apply sorted_cons.
        -- apply slr_length_eq.
           ++ unfold str_aaaa, str_cccc. simpl. reflexivity.
           ++ apply llr_lt. simpl. reflexivity.
        -- apply sorted_one.
Qed.