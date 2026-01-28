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

(* Test case: input = ["Ia"], output = false *)
Example test_palindrome_Ia : is_palindrome_spec "Ia" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Ia" to "aI" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Ia" = "aI" *)
  split.
  - (* Left to Right: false = true -> "Ia" = "aI" *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
  - (* Right to Left: "Ia" = "aI" -> false = true *)
    intros H.
    (* "Ia" = "aI" implies 'I' = 'a', which is false *)
    inversion H.
Qed.