Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.

Open Scope string_scope.
Open Scope char_scope.

Definition ascii_of_bool (b : bool) : ascii :=
  if b then "1"%char else "0"%char.

Definition bool_of_ascii (c : ascii) : option bool :=
  if ascii_dec c "0"%char then Some false
  else if ascii_dec c "1"%char then Some true
  else None.

Definition xor_ascii (a b : ascii) : option ascii :=
  match bool_of_ascii a, bool_of_ascii b with
  | Some x, Some y => Some (ascii_of_bool (xorb x y))
  | _, _ => None
  end.

Fixpoint string_xor_prefix (a b r : string) : Prop :=
  match a, r with
  | EmptyString, EmptyString => True
  | String ca a', String cr r' =>
      exists cb b',
        b = String cb b' /\
        xor_ascii ca cb = Some cr /\
        string_xor_prefix a' b' r'
  | _, _ => False
  end.

Definition string_xor_spec (a b r : string) : Prop :=
  string_xor_prefix a b r.

Example test_xor_example : string_xor_spec "11011011" "01011010" "10000001".
Proof.
  (* Unfold the specification wrapper *)
  unfold string_xor_spec.
  
  (* Simplify the fixpoint computation based on the structure of 'a' and 'r' *)
  simpl.

  (* 
     The goal is a series of nested existential quantifiers and conjunctions.
     We need to prove that for each character in string 'a' and 'r', 
     there exists a corresponding character in 'b' such that the XOR condition holds.
     
     Since 'b' is a concrete string ("01011010"), we can repeatedly:
     1. Existentially instantiate the head character of the current remainder of 'b'.
     2. Existentially instantiate the tail string of the current remainder of 'b'.
     3. Prove the head/tail decomposition is correct (reflexivity).
     4. Prove the XOR calculation is correct (reflexivity).
     5. Move to the next character.
  *)
  repeat (eexists; eexists; split; [ reflexivity | split; [ reflexivity | ] ]).

  (* Finally, we reach the base case where a and r are EmptyString, which simplifies to True *)
  exact I.
Qed.