(* 导入必要的 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* 字典序比较 *)
Inductive string_le_rel : string -> string -> Prop :=
| slr_empty : forall s, string_le_rel EmptyString s
| slr_lt : forall c1 s1 c2 s2,
    nat_of_ascii c1 < nat_of_ascii c2 ->
    string_le_rel (String c1 s1) (String c2 s2)
| slr_eq : forall c s1 s2,
    string_le_rel s1 s2 ->
    string_le_rel (String c s1) (String c s2).

(* 检查字符是否在字符串中 *)
Inductive string_contains_rel (c : ascii) : string -> Prop :=
| scr_head : forall s, string_contains_rel c (String c s)
| scr_tail : forall x s, string_contains_rel c s -> string_contains_rel c (String x s).

(* 计算唯一字符数 *)
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

(* 输入单词列表需非空 *)
Definition problem_158_pre (words : list string) : Prop := words <> [].

(*
  find_max 函数的程序规约 (Spec)。
*)
Definition problem_158_spec (words : list string) (result : string) : Prop :=
  In result words /\
  forall w, In w words ->
    exists c_res c_w,
      count_unique_chars_rel result c_res /\
      count_unique_chars_rel w c_w /\
      (c_res > c_w \/ (c_res = c_w /\ string_le_rel result w)).

(* Helper lemma: string_le_rel is reflexive *)
Lemma string_le_rel_refl : forall s, string_le_rel s s.
Proof.
  induction s.
  - apply slr_empty.
  - apply slr_eq. apply IHs.
Qed.

(* Count unique chars for "string" = 6 *)
Lemma count_string : count_unique_chars_rel "string" 6.
Proof.
  apply cucr_new.
  - intro H. inversion H; subst; clear H.
    + inversion H1.
    + inversion H1; subst; clear H1.
      * inversion H3.
      * inversion H3; subst; clear H3.
        -- inversion H5.
        -- inversion H5; subst; clear H5.
           ++ inversion H7.
           ++ inversion H7; subst; clear H7.
              ** inversion H9.
              ** inversion H9.
  - apply cucr_new.
    + intro H. inversion H; subst; clear H.
      * inversion H1.
      * inversion H1; subst; clear H1.
        -- inversion H3.
        -- inversion H3; subst; clear H3.
           ++ inversion H5.
           ++ inversion H5; subst; clear H5.
              ** inversion H7.
              ** inversion H7.
    + apply cucr_new.
      * intro H. inversion H; subst; clear H.
        -- inversion H1.
        -- inversion H1; subst; clear H1.
           ++ inversion H3.
           ++ inversion H3; subst; clear H3.
              ** inversion H5.
              ** inversion H5.
      * apply cucr_new.
        -- intro H. inversion H; subst; clear H.
           ++ inversion H1.
           ++ inversion H1; subst; clear H1.
              ** inversion H3.
              ** inversion H3.
        -- apply cucr_new.
           ++ intro H. inversion H; subst; clear H.
              ** inversion H1.
              ** inversion H1.
           ++ apply cucr_new.
              ** intro H. inversion H.
              ** apply cucr_empty.
Qed.

(* Count unique chars for "name" = 4 *)
Lemma count_name : count_unique_chars_rel "name" 4.
Proof.
  apply cucr_new.
  - intro H. inversion H; subst; clear H.
    + inversion H1.
    + inversion H1; subst; clear H1.
      * inversion H3.
      * inversion H3; subst; clear H3.
        -- inversion H5.
        -- inversion H5.
  - apply cucr_new.
    + intro H. inversion H; subst; clear H.
      * inversion H1.
      * inversion H1; subst; clear H1.
        -- inversion H3.
        -- inversion H3.
    + apply cucr_new.
      * intro H. inversion H; subst; clear H.
        -- inversion H1.
        -- inversion H1.
      * apply cucr_new.
        -- intro H. inversion H.
        -- apply cucr_empty.
Qed.

(* Count unique chars for "of" = 2 *)
Lemma count_of : count_unique_chars_rel "of" 2.
Proof.
  apply cucr_new.
  - intro H. inversion H; subst; clear H.
    + inversion H1.
    + inversion H1.
  - apply cucr_new.
    + intro H. inversion H.
    + apply cucr_empty.
Qed.

Example test_problem_158 : problem_158_spec ["name"; "of"; "string"] "string".
Proof.
  unfold problem_158_spec.
  split.
  - simpl. right. right. left. reflexivity.
  - intros w Hw.
    simpl in Hw.
    destruct Hw as [Hw | [Hw | [Hw | Hw]]].
    + subst w.
      exists 6, 4.
      split. { apply count_string. }
      split. { apply count_name. }
      left. lia.
    + subst w.
      exists 6, 2.
      split. { apply count_string. }
      split. { apply count_of. }
      left. lia.
    + subst w.
      exists 6, 6.
      split. { apply count_string. }
      split. { apply count_string. }
      right. split. { reflexivity. } { apply string_le_rel_refl. }
    + contradiction.
Qed.