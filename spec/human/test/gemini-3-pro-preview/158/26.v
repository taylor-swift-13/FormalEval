Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

(* 字典序比较 *)
Fixpoint string_le (s1 s2 : string) : Prop :=
  match s1, s2 with
  | EmptyString, _ => True
  | String _ _, EmptyString => False
  | String c1 s1', String c2 s2' =>
      (nat_of_ascii c1 < nat_of_ascii c2) \/ (c1 = c2 /\ string_le s1' s2')
  end.

(* 检查字符是否在字符串中 *)
Fixpoint string_contains (c : ascii) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c' s' => if Ascii.eqb c c' then true else string_contains c s'
  end.

(* 计算唯一字符数 *)
Fixpoint count_unique_chars (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
      let n := count_unique_chars s' in
      if string_contains c s' then n else S n
  end.

(* 输入单词列表需非空 *)
Definition problem_158_pre (words : list string) : Prop := words <> [].

(*
  find_max 函数的程序规约 (Spec)。
*)
Definition problem_158_spec (words : list string) (result : string) : Prop :=
  In result words /\
  forall w, In w words ->
    let c_res := count_unique_chars result in
    let c_w := count_unique_chars w in
    c_res > c_w \/ (c_res = c_w /\ string_le result w).

(* Helper tactic to solve string_le on concrete strings *)
Ltac solve_string_le :=
  repeat (
    simpl;
    match goal with
    | [ |- True ] => exact I
    | [ |- False ] => contradiction
    | [ |- _ \/ _ ] => 
        try (left; simpl; lia); 
        try (right; split; [reflexivity | ])
    end).

Example test_case_1 : problem_158_spec ["abcdefg"; "qrstuvwxyz"; "qrstuvwxyz"] "qrstuvwxyz".
Proof.
  unfold problem_158_spec.
  split.
  - (* Part 1: result is in the list *)
    simpl. right. left. reflexivity.
  - (* Part 2: result is max unique chars or lexicographically first among max *)
    intros w H.
    simpl in H.
    destruct H as [H_abc | [H_qrst1 | [H_qrst2 | H_empty]]].
    + (* Case: w = "abcdefg" *)
      subst w.
      left.
      compute.
      lia.
    + (* Case: w = "qrstuvwxyz" *)
      subst w.
      right.
      split.
      * reflexivity.
      * solve_string_le.
    + (* Case: w = "qrstuvwxyz" *)
      subst w.
      right.
      split.
      * reflexivity.
      * solve_string_le.
    + (* Case: Empty list tail *)
      contradiction.
Qed.