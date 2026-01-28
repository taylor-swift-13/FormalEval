(* 导入必要的 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Import ListNotations.

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

(* 规约 Specification *)
Definition problem_158_spec (words : list string) (result : string) : Prop :=
  In result words /\
  forall w, In w words ->
    let c_res := count_unique_chars result in
    let c_w := count_unique_chars w in
    c_res > c_w \/ (c_res = c_w /\ string_le result w).

(* 明确写出字符串定义（避免自动解析错误） *)
Definition s_name : string := String "n"%char (String "a"%char (String "m"%char (String "e"%char EmptyString))).
Definition s_of : string := String "o"%char (String "f"%char EmptyString).
Definition s_string : string := String "s"%char (String "t"%char (String "r"%char (String "i"%char (String "n"%char (String "g"%char EmptyString))))).

Example test_case_1 :
  problem_158_spec [s_name; s_of; s_string] s_string.
Proof.
  unfold problem_158_spec.
  split.
  - (* result in words *)
    simpl. left. reflexivity.
  - intros w Hw.
    simpl in Hw.
    destruct Hw as [Hw | [Hw | [Hw | Hw]]]; try contradiction.
    + (* w = s_name *)
      subst w.
      simpl.
      (* 计算 count_unique_chars s_string *)
      assert (Hcount_str : count_unique_chars s_string = 6).
      { reflexivity. }
      (* 计算 count_unique_chars s_name *)
      assert (Hcount_name : count_unique_chars s_name = 4).
      { reflexivity. }
      left. lia.
    + (* w = s_of *)
      subst w.
      simpl.
      assert (Hcount_str : count_unique_chars s_string = 6).
      { reflexivity. }
      assert (Hcount_of : count_unique_chars s_of = 2).
      { reflexivity. }
      left. lia.
    + (* w = s_string *)
      subst w.
      simpl.
      right.
      split.
      * (* c_res = c_w *)
        reflexivity.
      * (* string_le s_string s_string (lexicographically less-or-equal) for same string is True *)
        induction s_string as [| c s IH].
        -- simpl. trivial.
        -- simpl. left. lia.
Qed.