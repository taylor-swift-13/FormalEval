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

Example problem_64_example_applebaglueaeiye_nat: problem_64_spec "applebaglueaeiye" 9%nat.
Proof.
  unfold problem_64_spec.
  set (s1 := String "e"%char "").
  assert (H1: vowels_count_rel s1 1%nat).
  { apply vcr_vowel; [apply ivc_e | apply vcr_empty]. }
  set (s2 := String "y"%char s1).
  assert (H2: vowels_count_rel s2 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H1.
  }
  set (s3 := String "i"%char s2).
  assert (H3: vowels_count_rel s3 2%nat).
  { apply vcr_vowel; [apply ivc_i | exact H2]. }
  set (s4 := String "e"%char s3).
  assert (H4: vowels_count_rel s4 3%nat).
  { apply vcr_vowel; [apply ivc_e | exact H3]. }
  set (s5 := String "a"%char s4).
  assert (H5: vowels_count_rel s5 4%nat).
  { apply vcr_vowel; [apply ivc_a | exact H4]. }
  set (s6 := String "e"%char s5).
  assert (H6: vowels_count_rel s6 5%nat).
  { apply vcr_vowel; [apply ivc_e | exact H5]. }
  set (s7 := String "u"%char s6).
  assert (H7: vowels_count_rel s7 6%nat).
  { apply vcr_vowel; [apply ivc_u | exact H6]. }
  set (s8 := String "l"%char s7).
  assert (H8: vowels_count_rel s8 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H7.
  }
  set (s9 := String "g"%char s8).
  assert (H9: vowels_count_rel s9 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H8.
  }
  set (s10 := String "a"%char s9).
  assert (H10: vowels_count_rel s10 7%nat).
  { apply vcr_vowel; [apply ivc_a | exact H9]. }
  set (s11 := String "b"%char s10).
  assert (H11: vowels_count_rel s11 7%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H10.
  }
  set (s12 := String "e"%char s11).
  assert (H12: vowels_count_rel s12 8%nat).
  { apply vcr_vowel; [apply ivc_e | exact H11]. }
  set (s13 := String "l"%char s12).
  assert (H13: vowels_count_rel s13 8%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H12.
  }
  set (s14 := String "p"%char s13).
  assert (H14: vowels_count_rel s14 8%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H13.
  }
  set (s15 := String "p"%char s14).
  assert (H15: vowels_count_rel s15 8%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact H14.
  }
  apply vcr_vowel.
  - apply ivc_a.
  - exact H15.
Qed.

Example problem_64_example_applebaglueaeiye_Z: exists n, problem_64_spec "applebaglueaeiye" n /\ (Z.of_nat n = 9%Z).
Proof.
  exists 9%nat.
  split.
  - apply problem_64_example_applebaglueaeiye_nat.
  - reflexivity.
Qed.