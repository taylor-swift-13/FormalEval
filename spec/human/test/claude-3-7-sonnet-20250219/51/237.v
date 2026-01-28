Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Fixpoint filter_string (f : ascii -> bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if f c then String c (filter_string f s') else filter_string f s'
  end.

Definition problem_51_pre (input : string) : Prop := True.

Definition problem_51_spec (input : string) (output : string) : Prop :=
  output = filter_string (fun c => negb (is_vowel c)) input.

Example test_remove_vowels_example :
  problem_51_spec "The quick brown fox jumps over the lazdog." "Th qck brwn fx jmps vr th lzdg.".
Proof.
  unfold problem_51_spec.
  simpl.

  (* Step-by-step simplification of filter_string (negb (is_vowel)) on the input string: *)
  (* T (not vowel) -> keep T *)
  (* h (not vowel) -> keep h *)
  (* e (vowel) -> skip *)
  (*   (space) not vowel -> keep space *)
  (* q not vowel -> keep *)
  (* u vowel -> skip *)
  (* i vowel -> skip *)
  (* c not vowel -> keep *)
  (* k not vowel -> keep *)
  (*   space -> keep *)
  (* b not vowel -> keep *)
  (* r not vowel -> keep *)
  (* o vowel -> skip *)
  (* w not vowel -> keep *)
  (* n not vowel -> keep *)
  (*   space -> keep *)
  (* f not vowel -> keep *)
  (* o vowel -> skip *)
  (* x not vowel -> keep *)
  (*   space -> keep *)
  (* j not vowel -> keep *)
  (* u vowel -> skip *)
  (* m not vowel -> keep *)
  (* p not vowel -> keep *)
  (* s not vowel -> keep *)
  (*   space -> keep *)
  (* o vowel -> skip *)
  (* v not vowel -> keep *)
  (* e vowel -> skip *)
  (* r not vowel -> keep *)
  (*   space -> keep *)
  (* t not vowel -> keep *)
  (* h not vowel -> keep *)
  (* e vowel -> skip *)
  (*   space -> keep *)
  (* l not vowel -> keep *)
  (* a vowel -> skip *)
  (* z not vowel -> keep *)
  (* d not vowel -> keep *)
  (* o vowel -> skip *)
  (* g not vowel -> keep *)
  (* . not vowel -> keep *)

  reflexivity.
Qed.