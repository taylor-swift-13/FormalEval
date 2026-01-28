Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* 辅助函数：字符是否在字符串中 *)
Fixpoint string_contains (c : ascii) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String x xs => if ascii_dec c x then true else string_contains c xs
  end.

(* 计算唯一字符数 *)
Fixpoint count_unique_chars (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => 
      if string_contains c s' 
      then count_unique_chars s'
      else S (count_unique_chars s')
  end.

(* 字典序比较 *)
Fixpoint string_le (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, _ => true
  | String c1 s1', String c2 s2' =>
      if ascii_dec c1 c2
      then string_le s1' s2'
      else if Nat.ltb (nat_of_ascii c1) (nat_of_ascii c2) then true else false
  | _, _ => false
  end.

(* find_max 实现 *)
Fixpoint find_max (words : list string) : string :=
  match words with
  | [] => EmptyString
  | [w] => w
  | w1 :: w2 :: ws =>
      let n1 := count_unique_chars w1 in
      let n2 := count_unique_chars w2 in
      if Nat.gtb n1 n2
      then find_max (w1 :: ws)
      else if Nat.gtb n2 n1
           then find_max (w2 :: ws)
           else if string_le w1 w2
                then find_max (w1 :: ws)
                else find_max (w2 :: ws)
  end.

(* 测试用例 *)
Example test_find_max : 
  find_max ["name"; "of"; "string"] = "string".
Proof.
  simpl.
  reflexivity.
Qed.