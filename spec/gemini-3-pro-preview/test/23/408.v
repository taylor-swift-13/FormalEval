Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Helper to construct string from ascii codes to avoid encoding issues *)
Fixpoint codes_to_string (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: t => String (ascii_of_nat n) (codes_to_string t)
  end.

(* 
   Constructing the string byte by byte to ensure it matches the length of 64.
   The input string contains Extended ASCII characters.
   Sequence:
   1. Space (32)
   2. ã (227)
   3. 10 Spaces (32)
   4. àèìòùáéíóúýâêîôûãñõäëïö (23 chars)
   5. àèìòùáéíóúýâêîôûãñõäëïö (23 chars)
   6. üÿçüÿç (6 chars)
   Total: 1 + 1 + 10 + 23 + 23 + 6 = 64.
*)
Definition input_codes : list nat :=
  [32; 227] ++
  [32; 32; 32; 32; 32; 32; 32; 32; 32; 32] ++
  [224; 232; 236; 242; 249; 225; 233; 237; 243; 250; 253; 226; 234; 238; 244; 251; 227; 241; 245; 228; 235; 239; 246] ++
  [224; 232; 236; 242; 249; 225; 233; 237; 243; 250; 253; 226; 234; 238; 244; 251; 227; 241; 245; 228; 235; 239; 246] ++
  [252; 255; 231; 252; 255; 231].

Definition input_string : string := codes_to_string input_codes.

(* Test case: input = [" ã          àèìòùáéíóúýâêîôûãñõäëïöàèìòùáéíóúýâêîôûãñõäëïöüÿçüÿç"], output = 64 *)
Example test_strlen_complex : strlen_spec input_string 64.
Proof.
  unfold strlen_spec.
  unfold input_string.
  vm_compute.
  reflexivity.
Qed.