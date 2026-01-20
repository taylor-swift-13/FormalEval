Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Arith.Arith Coq.Bool.Bool.
Open Scope string_scope.

Definition is_vowel_char (c:ascii) : bool :=
  match c with "a"%char|"e"%char|"i"%char|"o"%char|"u"%char|"A"%char|"E"%char|"I"%char|"O"%char|"U"%char => true | _ => false end.
Definition is_y (c:ascii) : bool := match c with "y"%char|"Y"%char => true | _ => false end.

Fixpoint vowels_count_func (s : string) : nat :=
  match s with EmptyString => 0 | String c s' => let rest := vowels_count_func s' in
      if is_vowel_char c then 1 + rest else if (is_y c) && (s' =? EmptyString) then 1 + rest else rest end.

Definition vowels_count_impl (s : string) : nat := vowels_count_func s.

Example vowels_count_impl_ACEDY: vowels_count_impl "ACEDY" = 3%nat.
Proof. reflexivity. Qed.

Definition vowels_count_spec (s : string) (output : nat) : Prop :=
  output = vowels_count_impl s.


