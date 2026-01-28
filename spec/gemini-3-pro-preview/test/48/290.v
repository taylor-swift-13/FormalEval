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

(* Test case: input = ["@@@@!3j"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "@@@@!3j" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> "@@@@!3j" = string_rev "@@@@!3j" *)
  split.
  - (* Left to Right: false = true -> "@@@@!3j" = string_rev "@@@@!3j" *)
    intros H.
    inversion H.
  - (* Right to Left: "@@@@!3j" = string_rev "@@@@!3j" -> false = true *)
    intros H.
    (* Simplify string_rev "@@@@!3j" to "j3!@@@@" *)
    simpl in H.
    (* "@@@@!3j" = "j3!@@@@" is false, derive contradiction *)
    discriminate.
Qed.