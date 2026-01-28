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

Example problem_64_example_ACEDY_nat: problem_64_spec "ACEDY" 3%nat.
Proof.
  unfold problem_64_spec.
  assert (Hy: vowels_count_rel (String "Y"%char "") 1%nat).
  { apply vcr_y_end; [apply iy_upper | reflexivity | reflexivity]. }
  assert (Hd: vowels_count_rel (String "D"%char (String "Y"%char "")) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Hy.
  }
  assert (He: vowels_count_rel (String "E"%char (String "D"%char (String "Y"%char ""))) 2%nat).
  { apply vcr_vowel; [apply ivc_E | exact Hd]. }
  assert (Hc: vowels_count_rel (String "C"%char (String "E"%char (String "D"%char (String "Y"%char "")))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact He.
  }
  apply vcr_vowel.
  - apply ivc_A.
  - exact Hc.
Qed.

Example problem_64_example_ACEDY_Z: exists n, problem_64_spec "ACEDY" n /\ (Z.of_nat n = 3%Z).
Proof.
  exists 3%nat.
  split.
  - apply problem_64_example_ACEDY_nat.
  - reflexivity.
Qed.