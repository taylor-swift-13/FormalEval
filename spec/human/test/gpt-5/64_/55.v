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

Example problem_64_example_aeuyaeibayoyuy_nat: problem_64_spec "aeuyaeibayoyuy" 10%nat.
Proof.
  unfold problem_64_spec.
  assert (Hy: vowels_count_rel (String "y"%char "") 1%nat).
  { apply vcr_y_end; [apply iy_lower | reflexivity | reflexivity]. }
  assert (Huy: vowels_count_rel (String "u"%char (String "y"%char "")) 2%nat).
  { apply vcr_vowel; [apply ivc_u | exact Hy]. }
  assert (Hyuy: vowels_count_rel (String "y"%char (String "u"%char (String "y"%char ""))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Huy.
  }
  assert (Hoyuy: vowels_count_rel (String "o"%char (String "y"%char (String "u"%char (String "y"%char "")))) 3%nat).
  { apply vcr_vowel; [apply ivc_o | exact Hyuy]. }
  assert (Hyoyuy: vowels_count_rel (String "y"%char (String "o"%char (String "y"%char (String "u"%char (String "y"%char ""))))) 3%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Hoyuy.
  }
  assert (Hayoyuy: vowels_count_rel (String "a"%char (String "y"%char (String "o"%char (String "y"%char (String "u"%char (String "y"%char ""))))) ) 4%nat).
  { apply vcr_vowel; [apply ivc_a | exact Hyoyuy]. }
  assert (Hbayoyuy: vowels_count_rel (String "b"%char (String "a"%char (String "y"%char (String "o"%char (String "y"%char (String "u"%char (String "y"%char ""))))))) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Hayoyuy.
  }
  assert (Hibayoyuy: vowels_count_rel (String "i"%char (String "b"%char (String "a"%char (String "y"%char (String "o"%char (String "y"%char (String "u"%char (String "y"%char "")))))))) 5%nat).
  { apply vcr_vowel; [apply ivc_i | exact Hbayoyuy]. }
  assert (Heibayoyuy: vowels_count_rel (String "e"%char (String "i"%char (String "b"%char (String "a"%char (String "y"%char (String "o"%char (String "y"%char (String "u"%char (String "y"%char ""))))))))) 6%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hibayoyuy]. }
  assert (Haeibayoyuy: vowels_count_rel (String "a"%char (String "e"%char (String "i"%char (String "b"%char (String "a"%char (String "y"%char (String "o"%char (String "y"%char (String "u"%char (String "y"%char "")))))))))) 7%nat).
  { apply vcr_vowel; [apply ivc_a | exact Heibayoyuy]. }
  assert (Hyaeibayoyuy: vowels_count_rel (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "b"%char (String "a"%char (String "y"%char (String "o"%char (String "y"%char (String "u"%char (String "y"%char ""))))))))))) 7%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Haeibayoyuy.
  }
  assert (Huyaeibayoyuy: vowels_count_rel (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "b"%char (String "a"%char (String "y"%char (String "o"%char (String "y"%char (String "u"%char (String "y"%char "")))))))))))) 8%nat).
  { apply vcr_vowel; [apply ivc_u | exact Hyaeibayoyuy]. }
  assert (Heuyaeibayoyuy: vowels_count_rel (String "e"%char (String "u"%char (String "y"%char (String "a"%char (String "e"%char (String "i"%char (String "b"%char (String "a"%char (String "y"%char (String "o"%char (String "y"%char (String "u"%char (String "y"%char ""))))))))))))) 9%nat).
  { apply vcr_vowel; [apply ivc_e | exact Huyaeibayoyuy]. }
  apply vcr_vowel.
  - apply ivc_a.
  - exact Heuyaeibayoyuy.
Qed.

Example problem_64_example_aeuyaeibayoyuy_Z: exists n, problem_64_spec "aeuyaeibayoyuy" n /\ (Z.of_nat n = 10%Z).
Proof.
  exists 10%nat.
  split.
  - apply problem_64_example_aeuyaeibayoyuy_nat.
  - reflexivity.
Qed.