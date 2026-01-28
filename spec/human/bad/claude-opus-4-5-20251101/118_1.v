Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.

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
    (exists c_prev c_next,
        String.get (i - 1) word = Some c_prev /\
        String.get i word = Some c_curr /\
        String.get (i + 1) word = Some c_next /\
        is_consonant c_prev /\ is_vowel c_curr /\ is_consonant c_next) /\
    result = String c_curr ""%string /\
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

Example test_yogurt : problem_118_spec "yogurt" "u".
Proof.
  unfold problem_118_spec.
  left.
  exists 3, "u"%char.
  split.
  - (* 1 <= 3 < 6 - 1 = 5 *)
    simpl. lia.
  - split.
    + (* exists c_prev c_next with the pattern *)
      exists "g"%char, "r"%char.
      split. { simpl. reflexivity. }
      split. { simpl. reflexivity. }
      split. { simpl. reflexivity. }
      split.
      * (* is_consonant "g" *)
        unfold is_consonant, is_alpha, is_vowel.
        simpl. split. right. lia. intro H. exact H.
      * split.
        -- (* is_vowel "u" *)
           unfold is_vowel. simpl. exact I.
        -- (* is_consonant "r" *)
           unfold is_consonant, is_alpha, is_vowel.
           simpl. split. right. lia. intro H. exact H.
    + split.
      * (* result = "u" *)
        reflexivity.
      * (* no j > 3 with j < 5 satisfies the pattern *)
        intros j [Hj1 Hj2].
        simpl in Hj2.
        (* j can only be 4 *)
        assert (j = 4) as Hj by lia. subst j.
        intro Hcontra.
        destruct Hcontra as [j_prev [j_curr [j_next [Hprev [Hcurr [Hnext [Hcons1 [Hvow Hcons2]]]]]]]].
        simpl in Hcurr.
        injection Hcurr as Hcurr.
        subst j_curr.
        (* j_curr = "r", but "r" is not a vowel *)
        unfold is_vowel in Hvow.
        simpl in Hvow.
        exact Hvow.
Qed.