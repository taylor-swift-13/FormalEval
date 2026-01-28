Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Arith.
Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.

Definition is_vowel (c : ascii) : Prop :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => True
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => True
  | _ => False
  end.

Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122).

Definition is_consonant (c : ascii) : Prop :=
  is_alpha c /\ ~ is_vowel c.

Definition problem_118_pre (word : string) : Prop :=
  let fix all_letters (w : string) : Prop :=
    match w with
    | EmptyString => True
    | String ch rest =>
        let n := nat_of_ascii ch in ((65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) /\ all_letters rest
    end in all_letters word.

Definition problem_118_spec (word: string) (result: string) : Prop :=
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

Example test_118_yogurt : problem_118_spec "yogurt"%string "u"%string.
Proof.
  unfold problem_118_spec.
  left.
  exists 3, ("u"%char).
  split.
  - simpl. lia.
  - split.
    + exists ("g"%char), ("r"%char).
      repeat split.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * unfold is_consonant.
        split.
        -- unfold is_alpha. simpl. right. split; lia.
        -- unfold is_vowel. simpl. intros H. exact H.
      * unfold is_vowel. simpl. exact I.
      * unfold is_consonant.
        split.
        -- unfold is_alpha. simpl. right. split; lia.
        -- unfold is_vowel. simpl. intros H. exact H.
    + simpl. reflexivity.
    + intros j Hj.
      simpl in Hj.
      assert (j = 4) by lia.
      subst j.
      intros Hex.
      destruct Hex as (j_prev & j_curr & j_next & Hprev & Hcurr & Hnext & Hcprev & Hvowel & Hcnext).
      simpl in Hcurr.
      inversion Hcurr. subst j_curr.
      simpl in Hvowel. exact Hvowel.
Qed.