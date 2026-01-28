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

Example problem_64_example_cmonkeyandy_nat: problem_64_spec "cmonkeyandy" 4%nat.
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
  assert (Ha: vowels_count_rel (String "a"%char (String "n"%char (String "d"%char (String "y"%char "")))) 2%nat).
  { apply vcr_vowel; [apply ivc_a | exact Hn]. }
  assert (Hy2: vowels_count_rel (String "y"%char (String "a"%char (String "n"%char (String "d"%char (String "y"%char ""))))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Ha.
  }
  assert (He: vowels_count_rel (String "e"%char (String "y"%char (String "a"%char (String "n"%char (String "d"%char (String "y"%char ""))))) ) 3%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hy2]. }
  assert (Hk: vowels_count_rel (String "k"%char (String "e"%char (String "y"%char (String "a"%char (String "n"%char (String "d"%char (String "y"%char "")))))) ) 3%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact He.
  }
  assert (Hn2: vowels_count_rel (String "n"%char (String "k"%char (String "e"%char (String "y"%char (String "a"%char (String "n"%char (String "d"%char (String "y"%char ""))))))) ) 3%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hk.
  }
  assert (Ho: vowels_count_rel (String "o"%char (String "n"%char (String "k"%char (String "e"%char (String "y"%char (String "a"%char (String "n"%char (String "d"%char (String "y"%char "")))))))) ) 4%nat).
  { apply vcr_vowel; [apply ivc_o | exact Hn2]. }
  assert (Hm: vowels_count_rel (String "m"%char (String "o"%char (String "n"%char (String "k"%char (String "e"%char (String "y"%char (String "a"%char (String "n"%char (String "d"%char (String "y"%char ""))))))))) ) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Ho.
  }
  assert (Hc: vowels_count_rel (String "c"%char (String "m"%char (String "o"%char (String "n"%char (String "k"%char (String "e"%char (String "y"%char (String "a"%char (String "n"%char (String "d"%char (String "y"%char "")))))))))) ) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hm.
  }
  exact Hc.
Qed.

Example problem_64_example_cmonkeyandy_Z: exists n, problem_64_spec "cmonkeyandy" n /\ (Z.of_nat n = 4%Z).
Proof.
  exists 4%nat.
  split.
  - apply problem_64_example_cmonkeyandy_nat.
  - reflexivity.
Qed.