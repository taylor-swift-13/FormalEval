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

Example problem_64_example_ctiparpodyecme_nat: problem_64_spec "ctiparpodyecme" 5%nat.
Proof.
  unfold problem_64_spec.
  assert (He0: vowels_count_rel (String "e"%char "") 1%nat).
  { apply vcr_vowel; [apply ivc_e | apply vcr_empty]. }
  assert (Hm: vowels_count_rel (String "m"%char (String "e"%char "")) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact He0.
  }
  assert (Hc1: vowels_count_rel (String "c"%char (String "m"%char (String "e"%char ""))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; discriminate Hs.
    - exact Hm.
  }
  assert (He1: vowels_count_rel (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))) 2%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hc1]. }
  assert (Hy1: vowels_count_rel (String "y"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact He1.
  }
  assert (Hd1: vowels_count_rel (String "d"%char (String "y"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))))) 2%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Hy1.
  }
  assert (Ho1: vowels_count_rel (String "o"%char (String "d"%char (String "y"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))))) 3%nat).
  { apply vcr_vowel; [apply ivc_o | exact Hd1]. }
  assert (Hp1: vowels_count_rel (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))))))) 3%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Ho1.
  }
  assert (Hr1: vowels_count_rel (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))))))) 3%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Hp1.
  }
  assert (Ha1: vowels_count_rel (String "a"%char (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))))))))) 4%nat).
  { apply vcr_vowel; [apply ivc_a | exact Hr1]. }
  assert (Hp2: vowels_count_rel (String "p"%char (String "a"%char (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))))))))) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Ha1.
  }
  assert (Hi1: vowels_count_rel (String "i"%char (String "p"%char (String "a"%char (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))))))))))) 5%nat).
  { apply vcr_vowel; [apply ivc_i | exact Hp2]. }
  assert (Ht1: vowels_count_rel (String "t"%char (String "i"%char (String "p"%char (String "a"%char (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))))))))))) 5%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Hi1.
  }
  assert (Hc0: vowels_count_rel (String "c"%char (String "t"%char (String "i"%char (String "p"%char (String "a"%char (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))))))))))))) 5%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy' Hs]; discriminate Hs.
    - exact Ht1.
  }
  exact Hc0.
Qed.

Example problem_64_example_ctiparpodyecme_Z: exists n, problem_64_spec "ctiparpodyecme" n /\ (Z.of_nat n = 5%Z).
Proof.
  exists 5%nat.
  split.
  - apply problem_64_example_ctiparpodyecme_nat.
  - reflexivity.
Qed.