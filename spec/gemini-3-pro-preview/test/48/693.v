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

(* Test case: input = ["Do"], output = false *)
Example test_palindrome_Do : is_palindrome_spec "Do" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Do" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Do" = "oD" *)
  split.
  - (* Left to Right: false = true -> "Do" = "oD" *)
    intros H.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: "Do" = "oD" -> false = true *)
    intros H.
    (* "Do" = "oD" is a contradiction because 'D' <> 'o' *)
    discriminate.
Qed.