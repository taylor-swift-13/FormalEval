Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Arith.Arith Coq.Bool.Bool.
Open Scope string_scope.

Definition is_vowel_char (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition is_y (c : ascii) : bool :=
  match c with
  | "y"%char | "Y"%char => true
  | _ => false
  end.

Fixpoint vowels_count_func (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
    let rest := vowels_count_func s' in
    if is_vowel_char c then
      1 + rest
    else
      if (is_y c) && (s' =? EmptyString) then
        1 + rest
      else
        rest
  end.

Definition vowels_count_impl (s : string) : nat :=
  vowels_count_func s.

Definition problem_64_pre (s : string) : Prop := True.

Definition problem_64_spec (s : string) (output : nat) : Prop :=
  output = vowels_count_impl s.

Example test_vowels_count_abcde :
  problem_64_spec "abcde" 2.
Proof.
  unfold problem_64_spec, vowels_count_impl.
  simpl.
  (* s = "abcde" = String "a" (String "b" (String "c" (String "d" (String "e" EmptyString)))) *)
  (* vowels_count_func "abcde" 
     = if is_vowel_char "a" then 1 + vowels_count_func "bcde" else ... *)
  (* is_vowel_char "a" = true *)
  assert (H1 : is_vowel_char "a" = true).
  { simpl. reflexivity. }
  rewrite H1.
  simpl.
  (* Now consider vowels_count_func "bcde" *)
  remember (vowels_count_func "bcde") as v_bcde eqn:Hv_bcde.
  (* Evaluate vowels_count_func "bcde" *)
  simpl in Hv_bcde.
  (* c = "b" *)
  (* is_vowel_char "b" = false *)
  (* is_y "b" = false *)
  (* s' = "cde" <> EmptyString *)
  (* So vowels_count_func "bcde" = vowels_count_func "cde" *)
  remember (vowels_count_func "cde") as v_cde eqn:Hv_cde.
  rewrite Hv_cde in Hv_bcde.
  simpl in Hv_cde.
  (* c = "c" *)
  (* is_vowel_char "c" = false *)
  (* is_y "c" = false *)
  (* s' = "de" <> EmptyString *)
  (* vowels_count_func "cde" = vowels_count_func "de" *)
  remember (vowels_count_func "de") as v_de eqn:Hv_de.
  rewrite Hv_de in Hv_cde.
  simpl in Hv_de.
  (* c = "d" *)
  (* is_vowel_char "d" = false *)
  (* is_y "d" = false *)
  (* s' = "e" <> EmptyString *)
  (* vowels_count_func "de" = vowels_count_func "e" *)
  remember (vowels_count_func "e") as v_e eqn:Hv_e.
  rewrite Hv_e in Hv_de.
  simpl in Hv_e.
  (* c = "e" *)
  (* is_vowel_char "e" = true *)
  (* vowels_count_func "e" = 1 + vowels_count_func EmptyString = 1 + 0 = 1 *)
  simpl.
  subst v_e.
  reflexivity.
  subst v_de.
  subst v_cde.
  subst v_bcde.
  simpl.
  reflexivity.
Qed.