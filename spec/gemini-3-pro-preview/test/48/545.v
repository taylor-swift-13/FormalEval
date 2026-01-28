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

(* Test case: input = ["d3!@@@2Z.z21nama.WAsnral,Dd3!f12zZ2@@@@!3j  d3!@@@2Zz21oeman,@@@2DoZz21o"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "d3!@@@2Z.z21nama.WAsnral,Dd3!f12zZ2@@@@!3j  d3!@@@2Zz21oeman,@@@2DoZz21o" false.
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
    (* Evaluate the reverse string computation in the hypothesis *)
    vm_compute in H.
    (* The hypothesis now asserts equality between two distinct strings *)
    discriminate.
Qed.