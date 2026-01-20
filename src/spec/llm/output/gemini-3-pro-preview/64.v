Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Open Scope string_scope.
Open Scope char_scope.

Definition is_standard_vowel (c : ascii) : bool :=
  match c with
  | "a" | "e" | "i" | "o" | "u" 
  | "A" | "E" | "I" | "O" | "U" => true
  | _ => false
  end.

Fixpoint count_standard_vowels (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (if is_standard_vowel c then 1 else 0) + count_standard_vowels s'
  end.

Definition is_y (c : ascii) : bool :=
  match c with
  | "y" | "Y" => true
  | _ => false
  end.

Definition last_char_is_y (s : string) : bool :=
  match s with
  | EmptyString => false
  | _ => match get (length s - 1) s with
         | Some c => is_y c
         | None => false
         end
  end.

Definition vowels_count_spec (s : string) (cnt : nat) : Prop :=
  cnt = count_standard_vowels s + (if last_char_is_y s then 1 else 0).

Example test_vowels_abcde : vowels_count_spec "abcde" 2.
Proof.
  (* Unfold the specification definition *)
  unfold vowels_count_spec.
  
  (* 
     Simplify the expression. 
     This will evaluate:
     1. count_standard_vowels "abcde" -> count of 'a' and 'e' -> 2
     2. length "abcde" -> 5
     3. 5 - 1 -> 4
     4. get 4 "abcde" -> Some "e"
     5. is_y "e" -> false
     6. last_char_is_y "abcde" -> false
     7. The if-statement reduces to 0
     8. 2 + 0 -> 2
  *)
  simpl.
  
  (* Verify that 2 = 2 *)
  reflexivity.
Qed.