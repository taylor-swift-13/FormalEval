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

Example test_remove_vowels_long :
  problem_51_spec "This is ahhellhellooellhellooi am using python Test!"
                "Ths s hhllhllllhll m sng pythn Tst!".
Proof.
  unfold problem_51_spec.
  simpl.

  (* Manual expansion of filter_string with negb(is_vowel) for the input string *)
  (* Stepwise filtering vowels from "This is ahhellhellooellhellooi am using python Test!" *)

  (* "T" is not vowel: keep *)
  (* "h" not vowel: keep *)
  (* "i" vowel: remove *)
  (* "s" not vowel: keep *)
  (* " " keep *)
  (* "i" vowel: remove *)
  (* "s" keep *)
  (* " " keep *)
  (* "a" vowel: remove *)
  (* "h" keep *)
  (* "h" keep *)
  (* "e" vowel: remove *)
  (* "l" keep *)
  (* "l" keep *)
  (* "h" keep *)
  (* "e" vowel: remove *)
  (* "l" keep *)
  (* "l" keep *)
  (* "o" vowel: remove *)
  (* "o" vowel: remove *)
  (* "e" vowel: remove *)
  (* "l" keep *)
  (* "l" keep *)
  (* "h" keep *)
  (* "e" vowel: remove *)
  (* "l" keep *)
  (* "l" keep *)
  (* "o" vowel: remove *)
  (* "o" vowel: remove *)
  (* "i" vowel: remove *)
  (* " " keep *)
  (* "a" vowel: remove *)
  (* "m" keep *)
  (* " " keep *)
  (* "u" vowel: remove *)
  (* "s" keep *)
  (* "i" vowel: remove *)
  (* "n" keep *)
  (* "g" keep *)
  (* " " keep *)
  (* "p" keep *)
  (* "y" keep *)
  (* "t" keep *)
  (* "h" keep *)
  (* "o" vowel: remove *)
  (* "n" keep *)
  (* " " keep *)
  (* "T" keep *)
  (* "e" vowel: remove *)
  (* "s" keep *)
  (* "t" keep *)
  (* "!" keep *)

  reflexivity.
Qed.