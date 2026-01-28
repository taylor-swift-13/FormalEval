Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Bool.Bool.
Require Import Lia.

Open Scope string_scope.

(* Auxiliary definitions *)

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
      let n := nat_of_ascii ch in
      ((65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) /\ all_letters rest
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

Example test_yogurt : problem_118_spec "yogurt" "u".
Proof.
  unfold problem_118_spec.
  left.
  (* Length of "yogurt" is 6 *)
  assert (Hlen: String.length "yogurt" = 6) by reflexivity.
  exists 3.
  exists "u"%char.
  split.
  - lia.
  - split.
    + exists "g"%char.
      exists "r"%char.
      repeat split.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * split.
        -- unfold is_consonant.
           split.
           ++ unfold is_alpha.
              simpl.
              lia.
           ++ unfold is_vowel.
              simpl.
              discriminate.
        -- split.
           ++ unfold is_vowel.
              simpl.
              trivial.
           ++ unfold is_consonant.
              split.
              ** unfold is_alpha.
                 simpl.
                 lia.
              ** unfold is_vowel.
                 simpl.
                 discriminate.
    + split.
      * simpl. reflexivity.
      * intros j Hbounds.
        (* The only j with 3 < j < 5 is j=4 *)
        assert (j = 4) by lia; subst j.
        intros [j_prev [j_curr [j_next [G1 [G2 [G3 [Hprev [Hcurr Hnext]]]]]]]].
        simpl in G1,G2,G3.
        inversion G2; subst j_curr.
        unfold is_vowel in Hcurr.
        simpl in Hcurr.
        contradiction.
Qed.