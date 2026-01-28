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

Example problem_64_example_cthelloiecanddyndyme_nat: problem_64_spec "cthelloiecanddyndyme" 6%nat.
Proof.
  unfold problem_64_spec.
  assert (He20: vowels_count_rel (String "e"%char "") 1%nat).
  { apply vcr_vowel; [apply ivc_e | apply vcr_empty]. }
  assert (Hm19: vowels_count_rel (String "m"%char (String "e"%char "")) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact He20.
  }
  assert (Hy18: vowels_count_rel (String "y"%char (String "m"%char (String "e"%char ""))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hm19.
  }
  assert (Hd17: vowels_count_rel (String "d"%char (String "y"%char (String "m"%char (String "e"%char "")))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hy18.
  }
  assert (Hn16: vowels_count_rel (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char ""))))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hd17.
  }
  assert (Hy15: vowels_count_rel (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char "")))))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hn16.
  }
  assert (Hd14: vowels_count_rel (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char ""))))))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hy15.
  }
  assert (Hd13: vowels_count_rel (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char "")))))))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hd14.
  }
  assert (Hn12: vowels_count_rel (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char ""))))))))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hd13.
  }
  assert (Ha11: vowels_count_rel (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char "")))))))))) 2%nat).
  { apply vcr_vowel; [apply ivc_a | exact Hn12]. }
  assert (Hc10: vowels_count_rel (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char ""))))))))))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Ha11.
  }
  assert (He9: vowels_count_rel (String "e"%char (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char "")))))))))))) 3%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hc10]. }
  assert (Hi8: vowels_count_rel (String "i"%char (String "e"%char (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char ""))))))))))))) 4%nat).
  { apply vcr_vowel; [apply ivc_i | exact He9]. }
  assert (Ho7: vowels_count_rel (String "o"%char (String "i"%char (String "e"%char (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char "")))))))))))))) 5%nat).
  { apply vcr_vowel; [apply ivc_o | exact Hi8]. }
  assert (Hl6: vowels_count_rel (String "l"%char (String "o"%char (String "i"%char (String "e"%char (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char ""))))))))))))))) 5%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Ho7.
  }
  assert (Hl5: vowels_count_rel (String "l"%char (String "l"%char (String "o"%char (String "i"%char (String "e"%char (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char "")))))))))))))))) 5%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hl6.
  }
  assert (He4: vowels_count_rel (String "e"%char (String "l"%char (String "l"%char (String "o"%char (String "i"%char (String "e"%char (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char ""))))))))))))))))) 6%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hl5]. }
  assert (Hh3: vowels_count_rel (String "h"%char (String "e"%char (String "l"%char (String "l"%char (String "o"%char (String "i"%char (String "e"%char (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char "")))))))))))))))))) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact He4.
  }
  assert (Ht2: vowels_count_rel (String "t"%char (String "h"%char (String "e"%char (String "l"%char (String "l"%char (String "o"%char (String "i"%char (String "e"%char (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "y"%char (String "n"%char (String "d"%char (String "y"%char (String "m"%char (String "e"%char ""))))))))))))))))))) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hh3.
  }
  apply vcr_other.
  - intros H; inversion H.
  - intros [Hy0 Hs]; discriminate Hs.
  - exact Ht2.
Qed.

Example problem_64_example_cthelloiecanddyndyme_Z: exists n, problem_64_spec "cthelloiecanddyndyme" n /\ (Z.of_nat n = 6%Z).
Proof.
  exists 6%nat.
  split.
  - apply problem_64_example_cthelloiecanddyndyme_nat.
  - reflexivity.
Qed.