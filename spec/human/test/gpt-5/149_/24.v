Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat Lia.
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
| sbslr_nil : forall filtered, sorted_by_string_le_rel filtered nil
| sbslr_single : forall filtered s, sorted_by_string_le_rel filtered (s :: nil)
| sbslr_cons : forall filtered s1 s2 tail,
    string_le_rel s1 s2 ->
    sorted_by_string_le_rel filtered (s2 :: tail) ->
    sorted_by_string_le_rel filtered (s1 :: s2 :: tail).

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  exists filtered, filter_even_length_rel input filtered /\
    sorted_by_string_le_rel filtered output.

Example problem_149_test_1 :
  problem_149_spec ["programming"%string; "python"%string; ""%string; "java"%string; "ruby"%string]
                   [""%string; "java"%string; "ruby"%string; "python"%string].
Proof.
  unfold problem_149_spec.
  exists ["python"%string; ""%string; "java"%string; "ruby"%string].
  split.
  - apply felr_drop.
    + unfold not; intros H. inversion H as [s Hev]. simpl in Hev. congruence.
    + apply felr_keep.
      * constructor. simpl. reflexivity.
      * apply felr_keep.
        -- constructor. simpl. reflexivity.
        -- apply felr_keep.
           ++ constructor. simpl. reflexivity.
           ++ apply felr_keep.
              ** constructor. simpl. reflexivity.
              ** apply felr_nil.
  - apply sbslr_cons.
    + apply slr_length_lt. simpl. lia.
    + apply sbslr_cons.
      * apply slr_length_eq. simpl. reflexivity. apply llr_lt. simpl. reflexivity.
      * apply sbslr_cons.
        -- apply slr_length_lt. simpl. lia.
        -- apply sbslr_single.
Qed.