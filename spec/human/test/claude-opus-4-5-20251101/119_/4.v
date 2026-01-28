Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Inductive check_parens_inner_rel : list ascii -> nat -> bool -> Prop :=
  | cpir_nil_zero : check_parens_inner_rel [] 0 true
  | cpir_nil_nonzero : forall n, n <> 0 -> check_parens_inner_rel [] n false
  | cpir_lparen : forall t counter result,
      check_parens_inner_rel t (S counter) result ->
      check_parens_inner_rel ("("%char :: t) counter result
  | cpir_rparen_zero : forall t counter,
      counter = 0 ->
      check_parens_inner_rel (")"%char :: t) counter false
  | cpir_rparen : forall t counter n' result,
      counter = S n' ->
      check_parens_inner_rel t n' result ->
      check_parens_inner_rel (")"%char :: t) counter result
  | cpir_other : forall c t counter result,
      c <> "("%char -> c <> ")"%char ->
      check_parens_inner_rel t counter result ->
      check_parens_inner_rel (c :: t) counter result.

Inductive is_balanced_rel : list ascii -> bool -> Prop :=
  | ibr_base : forall l result, check_parens_inner_rel l 0 result -> is_balanced_rel l result.

Inductive concat_rel : list ascii -> list ascii -> list ascii -> Prop :=
  | concr_base : forall l1 l2, concat_rel l1 l2 (l1 ++ l2).

Definition problem_119_pre (inputs : list string) : Prop :=
  length inputs = 2 /\ Forall (fun s =>
    let l := list_ascii_of_string s in
    Forall (fun c => c = "("%char \/ c = ")"%char) l) inputs.

Definition problem_119_spec (inputs : list string) (output : string) : Prop :=
  (exists s1 s2 s12,
     map list_ascii_of_string inputs = [s1; s2] /\
     concat_rel s1 s2 s12 /\
     is_balanced_rel s12 true /\
     output = "Yes") \/
  (exists s1 s2 s21,
     map list_ascii_of_string inputs = [s1; s2] /\
     concat_rel s2 s1 s21 /\
     is_balanced_rel s21 true /\
     output = "Yes") \/
  ((forall s1 s2, map list_ascii_of_string inputs <> [s1; s2] \/
    (forall s12, concat_rel s1 s2 s12 -> is_balanced_rel s12 false) /\
    (forall s21, concat_rel s2 s1 s21 -> is_balanced_rel s21 false)) /\
   output = "No").

Example test_119 : problem_119_spec [")())"; "(()()(" ] "Yes".
Proof.
  unfold problem_119_spec.
  right. left.
  exists [")"%char; "("%char; ")"%char; ")"%char].
  exists ["("%char; "("%char; ")"%char; "("%char; ")"%char; "("%char].
  exists ["("%char; "("%char; ")"%char; "("%char; ")"%char; "("%char; ")"%char; "("%char; ")"%char; ")"%char].
  split.
  - simpl. reflexivity.
  - split.
    + apply concr_base.
    + split.
      * apply ibr_base.
        apply cpir_lparen.
        apply cpir_lparen.
        apply cpir_rparen with (n' := 1).
        -- reflexivity.
        -- apply cpir_lparen.
           apply cpir_rparen with (n' := 1).
           ++ reflexivity.
           ++ apply cpir_lparen.
              apply cpir_rparen with (n' := 1).
              ** reflexivity.
              ** apply cpir_lparen.
                 apply cpir_rparen with (n' := 1).
                 --- reflexivity.
                 --- apply cpir_rparen with (n' := 0).
                     +++ reflexivity.
                     +++ apply cpir_nil_zero.
      * reflexivity.
Qed.