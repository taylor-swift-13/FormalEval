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
  match s with
  | EmptyString => None
  | String c s' => match n with
                   | 0 => Some c
                   | S n' => get_char s' n'
                   end
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
  | 0 => None
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

(* 证明示例 *)
Example test_album : get_closest_vowel "album" = "u"%string.
Proof.
  unfold get_closest_vowel, find_rightmost_cvc.
  simpl.
  unfold get_char; simpl.
  unfold is_valid_cvc_position; simpl.
  unfold is_consonant_bool, is_vowel_bool, is_alpha_bool; simpl.
  (* 计算字符串长度 *)
  assert (String.length "album" = 5) by reflexivity.
  (* 位置2: l-b-u *)
  (* 位置2索引 2,前字符是 'l' 位置1， 中间字符 'b' 位置2， 后字符 'u' 位置3 *)
  (* 检查位置2是否为有效CVC *)
  (* 位置索引： i=2 *)
  (* get_char s (2-1)= get_char s 1 = 'l' *)
  (* get_char s 2 = 'b' *)
  (* get_char s (2+1) = get_char s 3 = 'u' *)
  (* 判断 'l' 是辅音， 'b' 是辅音， 'u' 是元音 *)
  (* 但实际上 'l' 是辅音， 'b' 是辅音， 'u' 是元音 *)
  (* 位置2满足CVC模式 *)
  reflexivity.
Qed.

(* 额外的测试用例 *)
Example test_FULL : get_closest_vowel "FULL" = "U"%string.
Proof.
  unfold get_closest_vowel, find_rightmost_cvc.
  simpl.
  unfold get_char; simpl.
  unfold is_valid_cvc_position; simpl.
  unfold is_consonant_bool, is_vowel_bool, is_alpha_bool; simpl.
  reflexivity.
Qed.

Example test_quick : get_closest_vowel "quick" = ""%string.
Proof.
  unfold get_closest_vowel, find_rightmost_cvc.
  simpl.
  reflexivity.
Qed.

Example test_ab : get_closest_vowel "ab" = ""%string.
Proof.
  unfold get_closest_vowel, find_rightmost_cvc.
  simpl.
  reflexivity.
Qed.