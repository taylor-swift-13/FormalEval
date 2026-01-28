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

(* Test case: input = ["saw?12@zZ2@@@@!3j  12zZ2Panama21"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "saw?12@zZ2@@@@!3j  12zZ2Panama21" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> "saw..." = string_rev "saw..." *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
  - (* Right to Left: "saw..." = string_rev "saw..." -> false = true *)
    intros H.
    (* Compute the string reversal in the hypothesis to reveal the mismatch *)
    vm_compute in H.
    (* The strings are distinct, so equality is impossible *)
    discriminate H.
Qed.