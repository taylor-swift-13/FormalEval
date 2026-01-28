Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Arith.Arith Coq.Bool.Bool.
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

Lemma not_vowel_b : ~ is_vowel_char "b"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_c : ~ is_vowel_char "c"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_d : ~ is_vowel_char "d"%char.
Proof. intro H; inversion H. Qed.

Lemma not_y_b : ~ is_y "b"%char.
Proof. intro H; inversion H. Qed.

Lemma not_y_c : ~ is_y "c"%char.
Proof. intro H; inversion H. Qed.

Lemma not_y_d : ~ is_y "d"%char.
Proof. intro H; inversion H. Qed.

Example problem_64_test1 : problem_64_spec "abcde" 2%nat.
Proof.
  unfold problem_64_spec.
  (* "abcde" has vowels: a, e -> count = 2 *)
  
  (* 'a' is a vowel, so we use vcr_vowel *)
  apply vcr_vowel.
  { apply ivc_a. }
  (* Now we need to show vowels_count_rel "bcde" 1 *)
  
  (* 'b' is not a vowel and not y at end *)
  apply vcr_other.
  { apply not_vowel_b. }
  { intro H. destruct H as [Hy _]. inversion Hy. }
  (* Now we need to show vowels_count_rel "cde" 1 *)
  
  (* 'c' is not a vowel and not y at end *)
  apply vcr_other.
  { apply not_vowel_c. }
  { intro H. destruct H as [Hy _]. inversion Hy. }
  (* Now we need to show vowels_count_rel "de" 1 *)
  
  (* 'd' is not a vowel and not y at end *)
  apply vcr_other.
  { apply not_vowel_d. }
  { intro H. destruct H as [Hy _]. inversion Hy. }
  (* Now we need to show vowels_count_rel "e" 1 *)
  
  (* 'e' is a vowel *)
  apply vcr_vowel.
  { apply ivc_e. }
  (* Now we need to show vowels_count_rel "" 0 *)
  
  apply vcr_empty.
Qed.