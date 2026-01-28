Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.

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
  (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122).

(* 定义：检查一个字符是否为辅音 *)
Definition is_consonant (c : ascii) : Prop :=
  is_alpha c /\ ~ is_vowel c.

(* 输入字符串只包含英文字母 *)
Definition problem_118_pre (word : string) : Prop :=
  let fix all_letters (w : string) : Prop :=
    match w with
    | EmptyString => True
    | String ch rest =>
        let n := nat_of_ascii ch in ((65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) /\ all_letters rest
    end in all_letters word.

Definition problem_118_spec (word: string) (result: string) : Prop :=
  (* 情况一：找到了符合条件的元音 *)
  (exists i c_curr,
    1 <= i < String.length word - 1 /\
    (*
     * 断言在 i-1, i, i+1 的位置上确实存在字符 (c_prev, c_curr, c_next)，
     * 并且这些字符满足 "辅音-元音-辅音" 的模式。
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

Example test_yogurt: problem_118_spec "yogurt" "u".
Proof.
  unfold problem_118_spec.
  left.
  exists 3, "u"%char.
  split.
  - (* Index bounds check: 1 <= 3 < 5 *)
    simpl. lia.
  - split.
    + (* Pattern check: consonant-vowel-consonant at index 3 *)
      exists "g"%char, "r"%char.
      split. { reflexivity. } (* get 2 = "g" *)
      split. { reflexivity. } (* get 3 = "u" *)
      split. { reflexivity. } (* get 4 = "r" *)
      split.
      * (* "g" is consonant *)
        unfold is_consonant. split.
        -- unfold is_alpha. simpl. lia.
        -- unfold is_vowel. simpl. tauto.
      * split.
        -- (* "u" is vowel *)
           unfold is_vowel. simpl. tauto.
        -- (* "r" is consonant *)
           unfold is_consonant. split.
           ++ unfold is_alpha. simpl. lia.
           ++ unfold is_vowel. simpl. tauto.
    + split.
      * (* Result string matches *)
        reflexivity.
      * (* Maximality check: no match for j > 3 *)
        intros j Hrange.
        simpl in Hrange.
        (* The only integer j satisfying 3 < j < 5 is j = 4 *)
        assert (j = 4) by lia. subst j.
        intro Hcontra.
        destruct Hcontra as [j_prev [j_curr [j_next [Hprev [Hcurr [Hnext [Hcons_prev [Hvow_curr Hcons_next]]]]]]]].
        (* At index 4, character is "r" *)
        simpl in Hcurr. inversion Hcurr. subst j_curr.
        (* "r" is not a vowel, so Hvow_curr is False *)
        unfold is_vowel in Hvow_curr. simpl in Hvow_curr. contradiction.
Qed.