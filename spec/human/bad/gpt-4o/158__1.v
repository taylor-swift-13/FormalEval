(* 导入必要的 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
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

(* 具体的测试案例 *)
Example test_problem_158 : problem_158_spec ["name"; "of"; "string"] "string".
Proof.
  unfold problem_158_spec.
  split.
  - simpl. auto.
  - intros w H_in.
    destruct (string_dec w "string").
    + subst. exists 6, 6. split.
      * repeat (apply cucr_new; [intro; inversion H; subst |]).
        apply cucr_empty.
      * split.
        -- repeat (apply cucr_new; [intro; inversion H; subst |]).
           apply cucr_empty.
        -- right. split; [reflexivity | apply slr_eq; apply slr_empty].
    + destruct (string_dec w "name").
      * subst. exists 6, 4. split.
        -- repeat (apply cucr_new; [intro; inversion H; subst |]).
           apply cucr_empty.
        -- split.
           ++ repeat (apply cucr_new; [intro; inversion H; subst |]).
              apply cucr_empty.
           ++ left. lia.
      * destruct (string_dec w "of").
        -- subst. exists 6, 2. split.
           ++ repeat (apply cucr_new; [intro; inversion H; subst |]).
              apply cucr_empty.
           ++ split.
              ** repeat (apply cucr_new; [intro; inversion H; subst |]).
                 apply cucr_empty.
              ** left. lia.
        -- subst. exists 6, 0. split.
           ++ repeat (apply cucr_new; [intro; inversion H; subst |]).
              apply cucr_empty.
           ++ split.
              ** apply cucr_empty.
              ** left. lia.
Qed.