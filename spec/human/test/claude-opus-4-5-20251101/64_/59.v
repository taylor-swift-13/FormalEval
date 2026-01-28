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

Lemma not_vowel_y : ~ is_vowel_char "y"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_g : ~ is_vowel_char "g"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_l : ~ is_vowel_char "l"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_m : ~ is_vowel_char "m"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_n : ~ is_vowel_char "n"%char.
Proof. intro H; inversion H. Qed.

Lemma not_vowel_k : ~ is_vowel_char "k"%char.
Proof. intro H; inversion H. Qed.

Lemma not_y_g : ~ is_y "g"%char.
Proof. intro H; inversion H. Qed.

Lemma not_y_l : ~ is_y "l"%char.
Proof. intro H; inversion H. Qed.

Lemma not_y_m : ~ is_y "m"%char.
Proof. intro H; inversion H. Qed.

Lemma not_y_n : ~ is_y "n"%char.
Proof. intro H; inversion H. Qed.

Lemma not_y_k : ~ is_y "k"%char.
Proof. intro H; inversion H. Qed.

Example problem_64_test1 : problem_64_spec "aeiouyaeglumonkeyeiouy" 15%nat.
Proof.
  unfold problem_64_spec.
  apply vcr_vowel. { apply ivc_a. }
  apply vcr_vowel. { apply ivc_e. }
  apply vcr_vowel. { apply ivc_i. }
  apply vcr_vowel. { apply ivc_o. }
  apply vcr_vowel. { apply ivc_u. }
  apply vcr_other. { apply not_vowel_y. } { intro H. destruct H as [_ Hs]. discriminate Hs. }
  apply vcr_vowel. { apply ivc_a. }
  apply vcr_vowel. { apply ivc_e. }
  apply vcr_other. { apply not_vowel_g. } { intro H. destruct H as [Hy _]. inversion Hy. }
  apply vcr_other. { apply not_vowel_l. } { intro H. destruct H as [Hy _]. inversion Hy. }
  apply vcr_vowel. { apply ivc_u. }
  apply vcr_other. { apply not_vowel_m. } { intro H. destruct H as [Hy _]. inversion Hy. }
  apply vcr_vowel. { apply ivc_o. }
  apply vcr_other. { apply not_vowel_n. } { intro H. destruct H as [Hy _]. inversion Hy. }
  apply vcr_other. { apply not_vowel_k. } { intro H. destruct H as [Hy _]. inversion Hy. }
  apply vcr_vowel. { apply ivc_e. }
  apply vcr_other. { apply not_vowel_y. } { intro H. destruct H as [_ Hs]. discriminate Hs. }
  apply vcr_vowel. { apply ivc_e. }
  apply vcr_vowel. { apply ivc_i. }
  apply vcr_vowel. { apply ivc_o. }
  apply vcr_vowel. { apply ivc_u. }
  apply vcr_y_end. { apply iy_lower. } { reflexivity. } { reflexivity. }
Qed.