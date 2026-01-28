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

(* Test case: input = ["@@@@!33j"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "@@@@!33j" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "@@@@!33j" *)
  simpl.
  
  (* The goal becomes: false = true <-> "@@@@!33j" = "j33!@@@@" *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* Premise is false, so we can discriminate *)
    discriminate.
  - (* Right to Left: "@@@@!33j" = "j33!@@@@" -> ... *)
    intros H.
    (* The strings are distinct, so we can discriminate *)
    discriminate.
Qed.