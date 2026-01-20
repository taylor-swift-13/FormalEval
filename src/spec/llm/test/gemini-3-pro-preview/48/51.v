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

(* Test case: input = ["aaacaracecar"], output = false *)
Example test_palindrome_not : is_palindrome_spec "aaacaracecar" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> "aaacaracecar" = string_rev "aaacaracecar" *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: "aaacaracecar" = string_rev "aaacaracecar" -> false = true *)
    intros H.
    (* Simplify the reversal in the hypothesis *)
    simpl in H.
    (* H becomes "aaacaracecar" = "racecaracaaa", which is false *)
    discriminate.
Qed.