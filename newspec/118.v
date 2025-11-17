(* You are given a word. Your task is to find the closest vowel that stands between
two consonants from the right side of the word (case sensitive).

Vowels in the beginning and ending doesn't count. Return empty string if you didn't
find any vowel met the above condition.

You may assume that the given string contains English letter only.

Example:
get_closest_vowel("yogurt") ==> "u"
get_closest_vowel("FULL") ==> "U"
get_closest_vowel("quick") ==> ""
get_closest_vowel("ab") ==> ""*)

(* 导入所需的 Coq 库 *)
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Arith.
Require Import Coq.Logic.FunctionalExtensionality.

(* 输入字符串只包含英文字母 *)
Definition Pre (word : string) : Prop :=
  let fix all_letters (w : string) : Prop :=
    match w with
    | EmptyString => True
    | String ch rest =>
        let n := nat_of_ascii ch in (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) /\ all_letters rest
    end in all_letters word.

(*
 * 辅助定义
 *)

(* 定义：检查一个字符是否为元音（区分大小写） *)
Definition is_vowel (c : ascii) : Prop :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => True
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => True
  | _ => False
  end.

(* 定义：检查一个字符是否为英文字母 *)
Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (65 <= n <= 90) \/ (97 <= n <= 122).

(* 定义：检查一个字符是否为辅音 *)
Definition is_consonant (c : ascii) : Prop :=
  is_alpha c /\ ~ is_vowel c.


(*
 * 程序规约 (Program Specification)
 *)

(*
 * @brief get_closest_vowel_spec word result
 *
 * `word`: 输入的字符串。
 * `result`: 期望的输出结果，类型为 string。
 *
 * 这个规约断言 `result` 是 `word` 中从右边数起第一个位于两个辅音之间的元音
 * (包装成单字符字符串)，或者在找不到时为空字符串。
 *)
Definition get_closest_vowel_spec (word: string) (result: string) : Prop :=
  (* 情况一：找到了符合条件的元音 *)
  (exists i c_curr,
    1 <= i < String.length word - 1 /\
    (*
     * 断言在 i-1, i, i+1 的位置上确实存在字符 (c_prev, c_curr, c_next)，
     * 并且这些字符满足 "辅音-元音-辅音" 的模式。
     * 这是处理 `option ascii` 类型的关键。
     *)
    (exists c_prev c_next,
        String.get (i - 1) word = Some c_prev /\
        String.get i word = Some c_curr /\
        String.get (i + 1) word = Some c_next /\
        is_consonant c_prev /\ is_vowel c_curr /\ is_consonant c_next) /\
    result = String c_curr ""%string /\
    (* 并且，这是最右边（即索引最大）的一个 *)
    (forall j,
      i < j < String.length word - 1 ->
      ~ (exists j_prev j_curr j_next,
            String.get (j - 1) word = Some j_prev /\
            String.get j word = Some j_curr /\
            String.get (j + 1) word = Some j_next /\
            is_consonant j_prev /\ is_vowel j_curr /\ is_consonant j_next))
  )
  \/
  (* 情况二：不存在符合条件的元音 *)
  (
    (forall i,
      1 <= i < String.length word - 1 ->
      ~ (exists c_prev c_curr c_next,
            String.get (i - 1) word = Some c_prev /\
            String.get i word = Some c_curr /\
            String.get (i + 1) word = Some c_next /\
            is_consonant c_prev /\ is_vowel c_curr /\ is_consonant c_next)) /\
    result = ""%string
  ).