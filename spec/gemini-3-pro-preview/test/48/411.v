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

(* Test case: input = ["Tacogeese cEvA a12acoman, a splasn, geesea canal: PanamaTaco notil is a name od3!@@@zz21f a foeman, ass I live.a"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "Tacogeese cEvA a12acoman, a splasn, geesea canal: PanamaTaco notil is a name od3!@@@zz21f a foeman, ass I live.a" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: text = rev text -> false = true *)
    intros H.
    (* Compute the reverse of the string to reveal the inequality *)
    vm_compute in H.
    (* The strings are different, so equality is impossible *)
    discriminate.
Qed.