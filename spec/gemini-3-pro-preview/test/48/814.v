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

(* Test case: input = ["stTco"], output = false *)
Example test_palindrome_stTco : is_palindrome_spec "stTco" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "stTco" to "ocTts" *)
  simpl.
  
  (* The goal becomes: false = true <-> "stTco" = "ocTts" *)
  split.
  - (* Left to Right: false = true -> "stTco" = "ocTts" *)
    intros H.
    (* Premise is false, contradiction *)
    discriminate.
  - (* Right to Left: "stTco" = "ocTts" -> false = true *)
    intros H.
    (* Premise is false ("s" <> "o"), contradiction *)
    discriminate.
Qed.