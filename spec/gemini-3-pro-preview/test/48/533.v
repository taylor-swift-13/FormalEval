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

(* Test case: input = ["d3!@@@Taco cEvvil is a name of aPanama.sLmf12zZ2@@@@!3j  d3!@@@2Zzeman,or foeman, as I live.aZz21oeman,"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "d3!@@@Taco cEvvil is a name of aPanama.sLmf12zZ2@@@@!3j  d3!@@@2Zzeman,or foeman, as I live.aZz21oeman," false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> text = string_rev text *)
  split.
  - (* Left to Right: false = true -> text = string_rev text *)
    intros H.
    (* False = true is a contradiction *)
    inversion H.
  - (* Right to Left: text = string_rev text -> false = true *)
    intros H.
    (* Simplify the string reversal in the hypothesis *)
    simpl in H.
    (* The simplified hypothesis shows distinct strings (starting with 'd' vs ','), so equality is impossible *)
    discriminate.
Qed.