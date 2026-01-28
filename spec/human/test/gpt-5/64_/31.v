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

Example problem_64_example_glumonglluekeye_nat: problem_64_spec "glumonglluekeye" 6%nat.
Proof.
  unfold problem_64_spec.
  assert (He1: vowels_count_rel (String "e"%char "") 1%nat).
  { apply vcr_vowel; [apply ivc_e | apply vcr_empty]. }
  assert (Hy_e: vowels_count_rel (String "y"%char (String "e"%char "")) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact He1.
  }
  assert (He_ye: vowels_count_rel (String "e"%char (String "y"%char (String "e"%char ""))) 2%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hy_e]. }
  assert (Hk_eye: vowels_count_rel (String "k"%char (String "e"%char (String "y"%char (String "e"%char "")))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact He_ye.
  }
  assert (He_keye: vowels_count_rel (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char ""))))) 3%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hk_eye]. }
  assert (Hu_ekeye: vowels_count_rel (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char "")))))) 4%nat).
  { apply vcr_vowel; [apply ivc_u | exact He_keye]. }
  assert (Hl_uekeye: vowels_count_rel (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char ""))))))) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hu_ekeye.
  }
  assert (Hll_luekeye: vowels_count_rel (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char "")))))))) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hl_uekeye.
  }
  assert (Hg_lluekeye: vowels_count_rel (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char ""))))))))) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hll_luekeye.
  }
  assert (Hn_glluekeye: vowels_count_rel (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char "")))))))))) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hg_lluekeye.
  }
  assert (Ho_nglluekeye: vowels_count_rel (String "o"%char (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char ""))))))))))) 5%nat).
  { apply vcr_vowel; [apply ivc_o | exact Hn_glluekeye]. }
  assert (Hm_onglluekeye: vowels_count_rel (String "m"%char (String "o"%char (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char "")))))))))))) 5%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Ho_nglluekeye.
  }
  assert (Hu_monglluekeye: vowels_count_rel (String "u"%char (String "m"%char (String "o"%char (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char ""))))))))))))) 6%nat).
  { apply vcr_vowel; [apply ivc_u | exact Hm_onglluekeye]. }
  assert (Hl_umonglluekeye: vowels_count_rel (String "l"%char (String "u"%char (String "m"%char (String "o"%char (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char "")))))))))))))) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hu_monglluekeye.
  }
  assert (Hg_lumonglluekeye: vowels_count_rel (String "g"%char (String "l"%char (String "u"%char (String "m"%char (String "o"%char (String "n"%char (String "g"%char (String "l"%char (String "l"%char (String "u"%char (String "e"%char (String "k"%char (String "e"%char (String "y"%char (String "e"%char ""))))))))))))))) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hl_umonglluekeye.
  }
  exact Hg_lumonglluekeye.
Qed.

Example problem_64_example_glumonglluekeye_Z: exists n, problem_64_spec "glumonglluekeye" n /\ (Z.of_nat n = 6%Z).
Proof.
  exists 6%nat.
  split.
  - apply problem_64_example_glumonglluekeye_nat.
  - reflexivity.
Qed.