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

Example problem_64_example_canddaeyd_nat: problem_64_spec "canddaeyd" 3%nat.
Proof.
  unfold problem_64_spec.
  assert (Hd_end: vowels_count_rel (String "d"%char "") 0%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; inversion Hy.
    - apply vcr_empty.
  }
  assert (Hy_d: vowels_count_rel (String "y"%char (String "d"%char "")) 0%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hd_end.
  }
  assert (He_yd: vowels_count_rel (String "e"%char (String "y"%char (String "d"%char ""))) 1%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hy_d]. }
  assert (Ha_eyd: vowels_count_rel (String "a"%char (String "e"%char (String "y"%char (String "d"%char "")))) 2%nat).
  { apply vcr_vowel; [apply ivc_a | exact He_yd]. }
  assert (Hd_aeyd: vowels_count_rel (String "d"%char (String "a"%char (String "e"%char (String "y"%char (String "d"%char ""))))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Ha_eyd.
  }
  assert (Hdd_aeyd: vowels_count_rel (String "d"%char (String "d"%char (String "a"%char (String "e"%char (String "y"%char (String "d"%char "")))))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hd_aeyd.
  }
  assert (Hn_ddaeyd: vowels_count_rel (String "n"%char (String "d"%char (String "d"%char (String "a"%char (String "e"%char (String "y"%char (String "d"%char ""))))))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hdd_aeyd.
  }
  assert (Ha_nddaeyd: vowels_count_rel (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "a"%char (String "e"%char (String "y"%char (String "d"%char ""))))))) ) 3%nat).
  { apply vcr_vowel; [apply ivc_a | exact Hn_ddaeyd]. }
  assert (Hc_anddaeyd: vowels_count_rel (String "c"%char (String "a"%char (String "n"%char (String "d"%char (String "d"%char (String "a"%char (String "e"%char (String "y"%char (String "d"%char ""))))))))) 3%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Ha_nddaeyd.
  }
  exact Hc_anddaeyd.
Qed.

Example problem_64_example_canddaeyd_Z: exists n, problem_64_spec "canddaeyd" n /\ (Z.of_nat n = 3%Z).
Proof.
  exists 3%nat.
  split.
  - apply problem_64_example_canddaeyd_nat.
  - reflexivity.
Qed.