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

Example problem_64_example_candaeioyoyyndy_nat: problem_64_spec "candaeioyoyyndy" 7%nat.
Proof.
  unfold problem_64_spec.
  assert (Hy: vowels_count_rel (String "y"%char "") 1%nat).
  { apply vcr_y_end; [apply iy_lower | reflexivity | reflexivity]. }
  assert (Hd: vowels_count_rel (String "d"%char (String "y"%char "")) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hy.
  }
  assert (Hn: vowels_count_rel (String "n"%char (String "d"%char (String "y"%char ""))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hd.
  }
  assert (Hy2: vowels_count_rel (String "y"%char (String "n"%char (String "d"%char (String "y"%char "")))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hn.
  }
  assert (Hy3: vowels_count_rel (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char ""))))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hy2.
  }
  assert (Ho1: vowels_count_rel (String "o"%char (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char "")))))) 2%nat).
  { apply vcr_vowel; [apply ivc_o | exact Hy3]. }
  assert (Hy4: vowels_count_rel (String "y"%char (String "o"%char (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char ""))))))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Ho1.
  }
  assert (Ho2: vowels_count_rel (String "o"%char (String "y"%char (String "o"%char (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char "")))))))) 3%nat).
  { apply vcr_vowel; [apply ivc_o | exact Hy4]. }
  assert (Hi: vowels_count_rel (String "i"%char (String "o"%char (String "y"%char (String "o"%char (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char ""))))))))) 4%nat).
  { apply vcr_vowel; [apply ivc_i | exact Ho2]. }
  assert (He: vowels_count_rel (String "e"%char (String "i"%char (String "o"%char (String "y"%char (String "o"%char (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char "")))))))))) 5%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hi]. }
  assert (Ha1: vowels_count_rel (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "y"%char (String "o"%char (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char ""))))))))))) 6%nat).
  { apply vcr_vowel; [apply ivc_a | exact He]. }
  assert (Hd2: vowels_count_rel (String "d"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "y"%char (String "o"%char (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char "")))))))))))) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Ha1.
  }
  assert (Hn2: vowels_count_rel (String "n"%char (String "d"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "y"%char (String "o"%char (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char ""))))))))))))) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hd2.
  }
  assert (Ha2: vowels_count_rel (String "a"%char (String "n"%char (String "d"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "y"%char (String "o"%char (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char "")))))))))))))) 7%nat).
  { apply vcr_vowel; [apply ivc_a | exact Hn2]. }
  assert (Hc: vowels_count_rel (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "a"%char (String "e"%char (String "i"%char (String "o"%char (String "y"%char (String "o"%char (String "y"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char ""))))))))))))))) 7%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Ha2.
  }
  exact Hc.
Qed.

Example problem_64_example_candaeioyoyyndy_Z: exists n, problem_64_spec "candaeioyoyyndy" n /\ (Z.of_nat n = 7%Z).
Proof.
  exists 7%nat.
  split.
  - apply problem_64_example_candaeioyoyyndy_nat.
  - reflexivity.
Qed.