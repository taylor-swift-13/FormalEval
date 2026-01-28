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

(* Test case: input = ["EvTaco cEvil is a name of a foeman, as I live.atil is a name ofoeman, as I live."], output = false *)
Example test_palindrome_complex : is_palindrome_spec "EvTaco cEvil is a name of a foeman, as I live.atil is a name ofoeman, as I live." false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> text = string_rev text *)
  split.
  - (* Left to Right: false = true -> text = string_rev text *)
    intros H.
    discriminate.
  - (* Right to Left: text = string_rev text -> false = true *)
    intros H.
    (* Compute string_rev to show the strings are different *)
    compute in H.
    discriminate.
Qed.