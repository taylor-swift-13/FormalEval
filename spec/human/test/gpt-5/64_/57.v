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

Example problem_64_example_aeictiemeoappleuyaeiouy_nat: problem_64_spec "aeictiemeoappleuyaeiouy" 16%nat.
Proof.
  unfold problem_64_spec.
  assert (H1: vowels_count_rel (String "y"%char "") 1%nat).
  { apply vcr_y_end; [apply iy_lower | reflexivity | reflexivity]. }
  assert (H2: vowels_count_rel (String "u"%char (String "y"%char "")) 2%nat).
  { apply vcr_vowel; [apply ivc_u | exact H1]. }
  assert (H3: vowels_count_rel (String "o"%char (String "u"%char (String "y"%char ""))) 3%nat).
  { apply vcr_vowel; [apply ivc_o | exact H2]. }
  assert (H4: vowels_count_rel (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))) 4%nat).
  { apply vcr_vowel; [apply ivc_i | exact H3]. }
  assert (H5: vowels_count_rel (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))) 5%nat).
  { apply vcr_vowel; [apply ivc_e | exact H4]. }
  assert (H6: vowels_count_rel (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))) ) 6%nat).
  { apply vcr_vowel; [apply ivc_a | exact H5]. }
  assert (H7: vowels_count_rel (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H6.
  }
  assert (H8: vowels_count_rel (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))) 7%nat).
  { apply vcr_vowel; [apply ivc_u | exact H7]. }
  assert (H9: vowels_count_rel (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))) 8%nat).
  { apply vcr_vowel; [apply ivc_e | exact H8]. }
  assert (H10: vowels_count_rel (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))))) 8%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H9.
  }
  assert (H11: vowels_count_rel (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))))) 8%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H10.
  }
  assert (H12: vowels_count_rel (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))))))) 8%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H11.
  }
  assert (H13: vowels_count_rel (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))))))) 9%nat).
  { apply vcr_vowel; [apply ivc_a | exact H12]. }
  assert (H14: vowels_count_rel (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))))))))) 10%nat).
  { apply vcr_vowel; [apply ivc_o | exact H13]. }
  assert (H15: vowels_count_rel (String "e"%char (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))))))))) 11%nat).
  { apply vcr_vowel; [apply ivc_e | exact H14]. }
  assert (H16: vowels_count_rel (String "m"%char (String "e"%char (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))))))))))) 11%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H15.
  }
  assert (H17: vowels_count_rel (String "e"%char (String "m"%char (String "e"%char (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))))))))))) 12%nat).
  { apply vcr_vowel; [apply ivc_e | exact H16]. }
  assert (H18: vowels_count_rel (String "i"%char (String "e"%char (String "m"%char (String "e"%char (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))))))))))))) 13%nat).
  { apply vcr_vowel; [apply ivc_i | exact H17]. }
  assert (H19: vowels_count_rel (String "t"%char (String "i"%char (String "e"%char (String "m"%char (String "e"%char (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))))))))))))) 13%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H18.
  }
  assert (H20: vowels_count_rel (String "c"%char (String "t"%char (String "i"%char (String "e"%char (String "m"%char (String "e"%char (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))))))))))))))) 13%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H19.
  }
  assert (H21: vowels_count_rel (String "i"%char (String "c"%char (String "t"%char (String "i"%char (String "e"%char (String "m"%char (String "e"%char (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char ""))))))))))))))))))))) 14%nat).
  { apply vcr_vowel; [apply ivc_i | exact H20]. }
  assert (H22: vowels_count_rel (String "e"%char (String "i"%char (String "c"%char (String "t"%char (String "i"%char (String "e"%char (String "m"%char (String "e"%char (String "o"%char (String "a"%char (String "p"%char (String "p"%char (String "l"%char (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "u"%char (String "y"%char "")))))))))))))))))))))) 15%nat).
  { apply vcr_vowel; [apply ivc_e | exact H21]. }
  apply vcr_vowel.
  - apply ivc_a.
  - exact H22.
Qed.

Example problem_64_example_aeictiemeoappleuyaeiouy_Z: exists n, problem_64_spec "aeictiemeoappleuyaeiouy" n /\ (Z.of_nat n = 16%Z).
Proof.
  exists 16%nat.
  split.
  - apply problem_64_example_aeictiemeoappleuyaeiouy_nat.
  - reflexivity.
Qed.