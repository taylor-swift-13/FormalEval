Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Arith.Arith Coq.Bool.Bool Coq.ZArith.ZArith.
Open Scope string_scope.

Inductive is_vowel_char : ascii -> Prop :=
| ivc_a : is_vowel_char "a"%char
| ivc_e : is_vowel_char "e"%char
| ivc_i : is_vowel_char "i"%char
| ivc_o : is_vowel_char "o"%char
| ivc_u : is_vowel_char "u"%char
| ivc_A : is_vowel_char "A"%char
| ivc_E : is_vowel_char "E"%char
| ivc_I : is_vowel_char "I"%char
| ivc_O : is_vowel_char "O"%char
| ivc_U : is_vowel_char "U"%char.

Inductive is_y : ascii -> Prop :=
| iy_lower : is_y "y"%char
| iy_upper : is_y "Y"%char.

Inductive vowels_count_rel : string -> nat -> Prop :=
| vcr_empty : vowels_count_rel "" 0%nat
| vcr_vowel : forall c s n, is_vowel_char c -> vowels_count_rel s n -> vowels_count_rel (String c s) (S n)
| vcr_y_end : forall c s n, is_y c -> s = "" -> n = 0%nat -> vowels_count_rel (String c s) (S n)
| vcr_other : forall c s n, ~ is_vowel_char c -> ~ (is_y c /\ s = "") -> vowels_count_rel s n -> vowels_count_rel (String c s) n.

Definition problem_64_pre (s : string) : Prop := True.

Definition problem_64_spec (s : string) (output : nat) : Prop :=
  vowels_count_rel s output.

Example problem_64_example_aeioappleuyaeiiouy_nat: problem_64_spec "aeioappleuyaeiiouy" 14%nat.
Proof.
  unfold problem_64_spec.
  assert (Hy: vowels_count_rel (String "y"%char "") 1%nat).
  { apply vcr_y_end; [apply iy_lower | reflexivity | reflexivity]. }
  assert (Hu: vowels_count_rel (String "u"%char (String "y"%char "")) 2%nat).
  { apply vcr_vowel; [apply ivc_u | exact Hy]. }
  assert (Ho: vowels_count_rel (String "o"%char (String "u"%char (String "y"%char ""))) 3%nat).
  { apply vcr_vowel; [apply ivc_o | exact Hu]. }
  assert (Hi1: vowels_count_rel (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))) 4%nat).
  { apply vcr_vowel; [apply ivc_i | exact Ho]. }
  assert (Hi2: vowels_count_rel (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))) 5%nat).
  { apply vcr_vowel; [apply ivc_i | exact Hi1]. }
  assert (He1: vowels_count_rel (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))) 6%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hi2]. }
  assert (Ha1: vowels_count_rel (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))) 7%nat).
  { apply vcr_vowel; [apply ivc_a | exact He1]. }
  assert (Hy_mid: vowels_count_rel (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))) 7%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Ha1.
  }
  assert (Hu2: vowels_count_rel (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))) 8%nat).
  { apply vcr_vowel; [apply ivc_u | exact Hy_mid]. }
  assert (He2: vowels_count_rel (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))) ) 9%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hu2]. }
  assert (Hl: vowels_count_rel (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))))) 9%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact He2.
  }
  assert (Hp1: vowels_count_rel (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))))))) 9%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Hl.
  }
  assert (Hp2: vowels_count_rel (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))))))) 9%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Hp1.
  }
  assert (Ha2: vowels_count_rel (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))))))) ) 10%nat).
  { apply vcr_vowel; [apply ivc_a | exact Hp2]. }
  assert (Ho2: vowels_count_rel (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))))))))) ) 11%nat).
  { apply vcr_vowel; [apply ivc_o | exact Ha2]. }
  assert (Hi3: vowels_count_rel (String "i"%char (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))))))))) ) 12%nat).
  { apply vcr_vowel; [apply ivc_i | exact Ho2]. }
  assert (He3: vowels_count_rel (String "e"%char (String "i"%char (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))))))))))) ) 13%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hi3]. }
  apply vcr_vowel.
  - apply ivc_a.
  - exact He3.
Qed.

Example problem_64_example_aeioappleuyaeiiouy_Z: exists n, problem_64_spec "aeioappleuyaeiiouy" n /\ (Z.of_nat n = 14%Z).
Proof.
  exists 14%nat.
  split.
  - apply problem_64_example_aeioappleuyaeiiouy_nat.
  - reflexivity.
Qed.