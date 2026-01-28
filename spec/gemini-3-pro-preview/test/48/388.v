Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Open Scope string_scope.

(* Function definition as provided in the specification *)
Fixpoint string_rev (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (string_rev s') ++ (String c EmptyString)
  end.

(* Specification definition as provided *)
Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
  result = true <-> text = string_rev text.

(* Test case: input = ["Taco cEvil is a name of a foeman, as I live12zZ2@@@@!3orTaco.a"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "Taco cEvil is a name of a foeman, as I live12zZ2@@@@!3orTaco.a" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> text = string_rev text *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
  - (* Right to Left: text = string_rev text -> false = true *)
    intros H.
    (* Compute the reversal of the string to check equality *)
    vm_compute in H.
    (* The strings are distinct (starts with "T" vs "a"), so equality is a contradiction *)
    discriminate H.
Qed.