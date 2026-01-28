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

Definition string_le_bool (s1 s2 : string) : bool :=
  let n1 := String.length s1 in
  let n2 := String.length s2 in
  if Nat.ltb n1 n2 then true
  else if Nat.eqb n1 n2 then
         match String.compare s1 s2 with
         | Gt => false
         | _ => true
         end
       else false.

Fixpoint insert (s : string) (l : list string) : list string :=
  match l with
  | [] => [s]
  | h :: t => if string_le_bool s h then s :: h :: t else h :: insert s t
  end.

Fixpoint sort (l : list string) : list string :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Definition sorted_by_string_le_rel (input output : list string) : Prop :=
  output = sort input.

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  exists filtered, filter_even_length_rel input filtered /\
    sorted_by_string_le_rel filtered output.

Example problem_149_test : problem_149_spec ["apple"; "orange"; "banana"; "grapefruit"] ["banana"; "orange"; "grapefruit"].
Proof.
  unfold problem_149_spec.
  exists ["orange"; "banana"; "grapefruit"].
  split.
  - apply felr_drop.
    + intro H. inversion H. simpl in *. discriminate.
    + apply felr_keep.
      * apply helr_build. simpl. reflexivity.
      * apply felr_keep.
        -- apply helr_build. simpl. reflexivity.
        -- apply felr_keep.
           ++ apply helr_build. simpl. reflexivity.
           ++ apply felr_nil.
  - unfold sorted_by_string_le_rel. simpl. reflexivity.
Qed.