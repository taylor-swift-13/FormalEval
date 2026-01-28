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

Example problem_64_example_glumonglluekewyhyye_nat: problem_64_spec "glumonglluekewyhyye" 6%nat.
Proof.
  unfold problem_64_spec.
  assert (He: vowels_count_rel (String "e"%char "") 1%nat).
  { apply vcr_vowel; [apply ivc_e | apply vcr_empty]. }
  assert (Hy1: vowels_count_rel (String "y"%char (String "e"%char "")) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact He.
  }
  assert (Hy2: vowels_count_rel (String "y"%char (String "y"%char (String "e"%char ""))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hy1.
  }
  assert (Hh: vowels_count_rel (String "h"%char (String "y"%char (String "y"%char (String "e"%char "")))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hy2.
  }
  assert (Hy3: vowels_count_rel (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char ""))))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hh.
  }
  assert (Hw: vowels_count_rel (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char "")))))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hy3.
  }
  assert (He2: vowels_count_rel (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char ""))))))) 2%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hw]. }
  assert (Hk: vowels_count_rel (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char "")))))))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact He2.
  }
  assert (He3: vowels_count_rel (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char ""))))))))) 3%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hk]. }
  assert (Hu1: vowels_count_rel (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char ""))))))))) ) 4%nat).
  { apply vcr_vowel; [apply ivc_u | exact He3]. }
  assert (Hl1: vowels_count_rel (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char ""))))))))))) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hu1.
  }
  assert (Hl2: vowels_count_rel (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char "")))))))))))) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hl1.
  }
  assert (Hg1: vowels_count_rel (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char ""))))))))))))) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hl2.
  }
  assert (Hn: vowels_count_rel (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char "")))))))))))))) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hg1.
  }
  assert (Ho: vowels_count_rel (String "o"%char (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char ""))))))))))))))) 5%nat).
  { apply vcr_vowel; [apply ivc_o | exact Hn]. }
  assert (Hm: vowels_count_rel (String "m"%char (String "o"%char (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char "")))))))))))))))) 5%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Ho.
  }
  assert (Hu2: vowels_count_rel (String "u"%char (String "m"%char (String "o"%char (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char ""))))))))))))))))) 6%nat).
  { apply vcr_vowel; [apply ivc_u | exact Hm]. }
  assert (Hl3: vowels_count_rel (String "l"%char (String "u"%char (String "m"%char (String "o"%char (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char "")))))))))))))))))) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hu2.
  }
  assert (Hg2: vowels_count_rel (String "g"%char (String "l"%char (String "u"%char (String "m"%char (String "o"%char (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "w"%char (String "y"%char (String "h"%char (String "y"%char (String "y"%char (String "e"%char ""))))))))))))))))))) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hl3.
  }
  exact Hg2.
Qed.

Example problem_64_example_glumonglluekewyhyye_Z: exists n, problem_64_spec "glumonglluekewyhyye" n /\ (Z.of_nat n = 6%Z).
Proof.
  exists 6%nat.
  split.
  - apply problem_64_example_glumonglluekewyhyye_nat.
  - reflexivity.
Qed.