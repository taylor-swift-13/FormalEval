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

(* Test case: input = ["Wasc it a car or  a cat I saw?"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "Wasc it a car or  a cat I saw?" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev to constant string *)
  simpl.
  
  (* The goal becomes: false = true <-> "..." = "..." *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left: "..." = "..." -> false = true *)
    intros H.
    (* The strings are distinct, so equality is impossible *)
    discriminate H.
Qed.