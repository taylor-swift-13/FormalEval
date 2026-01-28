(* 导入必要的 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Open Scope string_scope.

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

(* Helper lemma for string_le reflexivity *)
Lemma string_le_refl : forall s, string_le s s.
Proof.
  induction s.
  - simpl. trivial.
  - simpl. right. split; [reflexivity | assumption].
Qed.

Example problem_158_test1 : problem_158_spec ("we" :: "are" :: "a" :: "mad" :: "nation" :: nil) "nation".
Proof.
  unfold problem_158_spec.
  split.
  - simpl. right. right. right. right. left. reflexivity.
  - intros w Hw.
    simpl in Hw.
    destruct Hw as [Hw | [Hw | [Hw | [Hw | [Hw | Hw]]]]].
    + subst w.
      simpl.
      left. lia.
    + subst w.
      simpl.
      left. lia.
    + subst w.
      simpl.
      left. lia.
    + subst w.
      simpl.
      left. lia.
    + subst w.
      simpl.
      right. split.
      * reflexivity.
      * simpl.
        right. split. reflexivity.
        right. split. reflexivity.
        right. split. reflexivity.
        right. split. reflexivity.
        right. split. reflexivity.
        right. split. reflexivity.
        exact I.
    + destruct Hw.
Qed.