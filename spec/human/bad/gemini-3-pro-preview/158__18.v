Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.

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

(* Tactic to prove a character is NOT in a string literal *)
Ltac solve_not_in :=
  intro H;
  repeat match goal with
  | [ H_in : string_contains_rel _ _ |- _ ] =>
      inversion H_in; subst; clear H_in; try discriminate
  end.

(* Tactic to prove count_unique_chars_rel for literals with unique chars *)
Ltac solve_count :=
  repeat (apply cucr_new; [ solve_not_in | ]);
  apply cucr_empty.

(* Tactic to prove string_le_rel reflexivity for literals *)
Ltac solve_le_refl :=
  repeat apply slr_eq;
  apply slr_empty.

Example test_problem_158 : problem_158_spec ["xyz"; "pqr"] "pqr".
Proof.
  unfold problem_158_spec.
  split.
  - (* Part 1: result is in the list *)
    simpl. right. left. reflexivity.
  - (* Part 2: result is max unique or lexicographically first among max *)
    intros w Hw.
    simpl in Hw.
    destruct Hw as [H_xyz | [H_pqr | H_empty]]; subst.
    
    + (* Case 1: w = "xyz" *)
      (* count("pqr") = 3, count("xyz") = 3 *)
      exists 3, 3.
      repeat split.
      * solve_count.
      * solve_count.
      * right. split.
        -- reflexivity.
        -- (* "pqr" < "xyz" because 'p' < 'x' *)
           apply slr_lt.
           simpl. lia.
      
    + (* Case 2: w = "pqr" *)
      (* count("pqr") = 3, count("pqr") = 3 *)
      exists 3, 3.
      repeat split.
      * solve_count.
      * solve_count.
      * right. split.
        -- reflexivity.
        -- solve_le_refl.
        
    + (* Case 3: Empty list tail (contradiction) *)
      contradiction.
Qed.