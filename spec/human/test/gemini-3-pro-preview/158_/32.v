Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.

Inductive string_le_rel : string -> string -> Prop :=
| slr_empty : forall s, string_le_rel EmptyString s
| slr_lt : forall c1 s1 c2 s2,
    nat_of_ascii c1 < nat_of_ascii c2 ->
    string_le_rel (String c1 s1) (String c2 s2)
| slr_eq : forall c s1 s2,
    string_le_rel s1 s2 ->
    string_le_rel (String c s1) (String c s2).

Inductive string_contains_rel (c : ascii) : string -> Prop :=
| scr_head : forall s, string_contains_rel c (String c s)
| scr_tail : forall x s, string_contains_rel c s -> string_contains_rel c (String x s).

Inductive count_unique_chars_rel : string -> nat -> Prop :=
| cucr_empty : count_unique_chars_rel EmptyString 0
| cucr_seen : forall c s n,
    string_contains_rel c s ->
    count_unique_chars_rel s n ->
    count_unique_chars_rel (String c s) n
| cucr_new : forall c s n,
    ~ string_contains_rel c s ->
    count_unique_chars_rel s n ->
    count_unique_chars_rel (String c s) (S n).

Definition problem_158_pre (words : list string) : Prop := words <> [].

Definition problem_158_spec (words : list string) (result : string) : Prop :=
  In result words /\
  forall w, In w words ->
    exists c_res c_w,
      count_unique_chars_rel result c_res /\
      count_unique_chars_rel w c_w /\
      (c_res > c_w \/ (c_res = c_w /\ string_le_rel result w)).

Ltac solve_not_in :=
  intro H;
  repeat match goal with
  | [ H_in : string_contains_rel _ _ |- _ ] =>
      inversion H_in; subst; clear H_in; try discriminate
  end.

Ltac solve_in :=
  repeat (apply scr_head || apply scr_tail).

Ltac solve_count :=
  repeat match goal with
  | [ |- count_unique_chars_rel EmptyString 0 ] => apply cucr_empty
  | [ |- count_unique_chars_rel (String _ _) _ ] =>
      first [
        apply cucr_new; [ solve [ solve_not_in ] | ] |
        apply cucr_seen; [ solve [ solve_in ] | ]
      ]
  end.

Ltac solve_le_refl :=
  repeat apply slr_eq;
  apply slr_empty.

Example test_problem_158 : problem_158_spec ["helloxyz"; "aaaa"; "helloxyz"] "helloxyz".
Proof.
  unfold problem_158_spec.
  split.
  - simpl. left. reflexivity.
  - intros w Hw.
    simpl in Hw.
    destruct Hw as [H_hello | [H_aaaa | [H_hello2 | H_empty]]]; subst.
    + exists 7, 7.
      repeat split.
      * solve_count.
      * solve_count.
      * right. split.
        -- reflexivity.
        -- solve_le_refl.
    + exists 7, 1.
      repeat split.
      * solve_count.
      * solve_count.
      * left. lia.
    + exists 7, 7.
      repeat split.
      * solve_count.
      * solve_count.
      * right. split.
        -- reflexivity.
        -- solve_le_refl.
    + contradiction.
Qed.