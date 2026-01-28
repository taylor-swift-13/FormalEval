Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Import ListNotations.

(* 辅助定义 - 布尔版本 *)
Definition is_vowel_bool (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition is_alpha_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <=? n) && (n <=? 90) || (97 <=? n) && (n <=? 122).

Definition is_consonant_bool (c : ascii) : bool :=
  is_alpha_bool c && negb (is_vowel_bool c).

(* 获取字符串字符的正确函数 *)
Fixpoint get_char (s : string) (n : nat) : option ascii :=
  match s, n with
  | EmptyString, _ => None
  | String c s', O => Some c
  | String c s', S n' => get_char s' n'
  end.

(* 检查索引是否在有效范围内 *)
Definition valid_index (i len : nat) : bool :=
  (0 <=? i) && (i <? len).

(* 检查是否为有效的CVC模式位置 *)
Definition is_valid_cvc_position (s : string) (i : nat) : bool :=
  let len := String.length s in
  if (1 <=? i) && (i <? len - 1) then
    match get_char s (i-1), get_char s i, get_char s (i+1) with
    | Some prev, Some curr, Some next =>
        is_consonant_bool prev && is_vowel_bool curr && is_consonant_bool next
    | _, _, _ => false
    end
  else
    false.

(* 从右向左寻找第一个有效的CVC位置 *)
Fixpoint find_rightmost_cvc_aux (s : string) (i : nat) : option nat :=
  match i with
  | O => None
  | S i' =>
      if is_valid_cvc_position s i then
        Some i
      else
        find_rightmost_cvc_aux s i'
  end.

Definition find_rightmost_cvc (s : string) : option nat :=
  let len := String.length s in
  if len <? 3 then
    None
  else
    find_rightmost_cvc_aux s (len - 2).

(* 主函数实现 *)
Definition get_closest_vowel (s : string) : string :=
  match find_rightmost_cvc s with
  | Some i =>
      match get_char s i with
      | Some c => String c EmptyString
      | None => EmptyString
      end
  | None => EmptyString
  end.

(* 重新定义第一个测试例，修正证明以避免焦点错误 *)
Example test_ba : get_closest_vowel "ba" = ""%string.
Proof.
  unfold get_closest_vowel, find_rightmost_cvc.
  simpl.
  reflexivity.
Qed.