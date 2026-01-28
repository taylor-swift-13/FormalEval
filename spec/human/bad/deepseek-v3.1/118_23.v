Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Import ListNotations.

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

Fixpoint get_char (s : string) (n : nat) : option ascii :=
  match s, n with
  | EmptyString, _ => None
  | String c s', O => Some c
  | String c s', S n' => get_char s' n'
  end.

Definition valid_index (i len : nat) : bool :=
  (0 <=? i) && (i <? len).

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

Definition get_closest_vowel (s : string) : string :=
  match find_rightmost_cvc s with
  | Some i =>
      match get_char s i with
      | Some c => String c EmptyString
      | None => EmptyString
      end
  | None => EmptyString
  end.

Example test_try : get_closest_vowel "try" = ""%string.
Proof.
  unfold get_closest_vowel, find_rightmost_cvc.
  simpl.
  unfold find_rightmost_cvc_aux.
  simpl.
  (* 计算字符串长度 *)
  compute.
  (* 字符串长度为3 *)
  assert (String.length "try" = 3) by reflexivity.
  (* 计算起始索引 *)
  remember (3 - 2) as start_index.
  (* 开始递归检查位置 1 *)
  unfold is_valid_cvc_position.
  simpl.
  (* 位置1: t, r, y *)
  (* get_char "try" 0 = Some "t" *)
  unfold get_char; simpl.
  rewrite Heqstart_index in *.
  remember (get_char "try" (start_index)) as c1.
  destruct c1 as [c1_val|]; try discriminate.
  (* get_char "try" 1 = Some "r" *)
  unfold get_char; simpl.
  find_rewrite.
  (* get_char "try" 2 = Some "y" *)
  unfold get_char; simpl.
  find_rewrite.
  (* "t" -> 116, "r" -> 114, "y" -> 121 *)
  assert (nat_of_ascii "t"%char = 116) by reflexivity.
  assert (nat_of_ascii "r"%char = 114) by reflexivity.
  assert (nat_of_ascii "y"%char = 121) by reflexivity.
  (* 位置1对应字符 'r'，其前后字符为 't' 和 'y' *)
  (* t: 116, y: 121 *)
  simpl.
  (* 判断字符属性 *)
  unfold is_consonant_bool, is_vowel_bool, is_alpha_bool; simpl.
  (* prev: 't' -> consonant *)
  assert (is_consonant_bool "t"%char = true) by (unfold is_consonant_bool, is_vowel_bool, is_alpha_bool; simpl; rewrite Heqn; reflexivity).
  (* curr: 'r' not vowel *)
  assert (is_vowel_bool "r"%char = false) by (unfold is_vowel_bool; simpl; rewrite Heqn; reflexivity).
  (* next: 'y' is vowel *)
  assert (is_vowel_bool "y"%char = false) by (unfold is_vowel_bool; simpl; rewrite Heqn; reflexivity).
  (* 综合判断 *)
  (* 由于中间字符 'r' 不是元音，整行成立了 *)
  (* 但我们想知道该位置是否满足 CVC *)
  (* condition: consonant - vowel - consonant *)
  (* 这里需要检查当前字符是不是元音，显然不是 *)
  (* 因此位置不满足条件 *)
  reflexivity.
Qed.