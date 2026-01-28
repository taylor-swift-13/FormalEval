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

Example problem_64_example_ctiparpodyaecme_nat: problem_64_spec "ctiparpodyaecme" 6%nat.
Proof.
  unfold problem_64_spec.
  assert (He1: vowels_count_rel (String "e"%char "") 1%nat).
  { apply vcr_vowel; [apply ivc_e | apply vcr_empty]. }
  assert (Hm: vowels_count_rel (String "m"%char (String "e"%char "")) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; inversion Hy.
    - exact He1.
  }
  assert (Hc1: vowels_count_rel (String "c"%char (String "m"%char (String "e"%char ""))) 1%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy Hs]; inversion Hy.
    - exact Hm.
  }
  assert (He2: vowels_count_rel (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))) 2%nat).
  { apply vcr_vowel; [apply ivc_e | exact Hc1]. }
  assert (Ha1: vowels_count_rel (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))) 3%nat).
  { apply vcr_vowel; [apply ivc_a | exact He2]. }
  assert (Hy: vowels_count_rel (String "y"%char (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))) ) 3%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; discriminate Hs.
    - exact Ha1.
  }
  assert (Hd: vowels_count_rel (String "d"%char (String "y"%char (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))))) ) 3%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; inversion Hy0.
    - exact Hy.
  }
  assert (Ho: vowels_count_rel (String "o"%char (String "d"%char (String "y"%char (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))))) ) 4%nat).
  { apply vcr_vowel; [apply ivc_o | exact Hd]. }
  assert (Hp1: vowels_count_rel (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))))))) ) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; inversion Hy0.
    - exact Ho.
  }
  assert (Hr: vowels_count_rel (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))))))) ) 4%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; inversion Hy0.
    - exact Hp1.
  }
  assert (Ha2: vowels_count_rel (String "a"%char (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))))))))) ) 5%nat).
  { apply vcr_vowel; [apply ivc_a | exact Hr]. }
  assert (Hp2: vowels_count_rel (String "p"%char (String "a"%char (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))))))) )) 5%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; inversion Hy0.
    - exact Ha2.
  }
  assert (Hi: vowels_count_rel (String "i"%char (String "p"%char (String "a"%char (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))))))))) ) 6%nat).
  { apply vcr_vowel; [apply ivc_i | exact Hp2]. }
  assert (Ht: vowels_count_rel (String "t"%char (String "i"%char (String "p"%char (String "a"%char (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char "")))))))))))) ) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; inversion Hy0.
    - exact Hi.
  }
  assert (Hc2: vowels_count_rel (String "c"%char (String "t"%char (String "i"%char (String "p"%char (String "a"%char (String "r"%char (String "p"%char (String "o"%char (String "d"%char (String "y"%char (String "a"%char (String "e"%char (String "c"%char (String "m"%char (String "e"%char ""))))))))))))) ) 6%nat).
  { apply vcr_other.
    - intros H; inversion H.
    - intros [Hy0 Hs]; inversion Hy0.
    - exact Ht.
  }
  exact Hc2.
Qed.

Example problem_64_example_ctiparpodyaecme_Z: exists n, problem_64_spec "ctiparpodyaecme" n /\ (Z.of_nat n = 6%Z).
Proof.
  exists 6%nat.
  split.
  - apply problem_64_example_ctiparpodyaecme_nat.
  - reflexivity.
Qed.