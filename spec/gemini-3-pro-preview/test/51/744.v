Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

(* Define the conversion functions which are not in the standard library *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: (list_ascii_of_string s')
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

Definition is_vowel (c : ascii) : bool :=
  existsb (fun v => Ascii.eqb c v) ["a"; "e"; "i"; "o"; "u"; "A"; "E"; "I"; "O"; "U"].

Definition remove_vowels_spec (text : string) (result : string) : Prop :=
  result = string_of_list_ascii (filter (fun c => negb (is_vowel c)) (list_ascii_of_string text)).

Example test_remove_vowels_1 : remove_vowels_spec "The qThe quick brown fox jumpseThe qThe quick brown fox jumpsexample@example.comThe over the lazy  dog.uick brown foxy g.xample@example.comThe over the lazy  dog.uick brown foxy g." "Th qTh qck brwn fx jmpsTh qTh qck brwn fx jmpsxmpl@xmpl.cmTh vr th lzy  dg.ck brwn fxy g.xmpl@xmpl.cmTh vr th lzy  dg.ck brwn fxy g.".
Proof.
  unfold remove_vowels_spec.
  reflexivity.
Qed.