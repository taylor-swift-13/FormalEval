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

(* Test case: input = ["12zZ2@@@@!@3TacZz2112zZ2@@@@!@3Taco notj  d3!@@@2DoZz212Zz21oeman,"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "12zZ2@@@@!@3TacZz2112zZ2@@@@!@3Taco notj  d3!@@@2DoZz212Zz21oeman," false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> text = string_rev text *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    inversion H.
  - (* Right to Left: text = string_rev text -> false = true *)
    intros H.
    (* Simplify the hypothesis to expose the mismatch *)
    simpl in H.
    (* The first characters differ ('1' vs ','), so inversion solves the contradiction *)
    inversion H.
Qed.