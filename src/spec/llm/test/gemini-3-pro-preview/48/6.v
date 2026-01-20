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

(* Test case: input = ["xywyz"], output = false *)
Example test_palindrome_xywyz : is_palindrome_spec "xywyz" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "xywyz" to "zywyx" *)
  simpl.
  
  (* The goal becomes: false = true <-> "xywyz" = "zywyx" *)
  split.
  - (* Left to Right: false = true -> "xywyz" = "zywyx" *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
  - (* Right to Left: "xywyz" = "zywyx" -> false = true *)
    intros H.
    (* "xywyz" = "zywyx" is a contradiction because the strings are distinct *)
    discriminate H.
Qed.