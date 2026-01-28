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

(* Test case: input = ["man,ATacogeesea cEvil is a namf12zZ2@@@man,Ae of a foemplaWasan, as I live.a man,  plan, a canal: PanamTacoaTaco"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "man,ATacogeesea cEvil is a namf12zZ2@@@man,Ae of a foemplaWasan, as I live.a man,  plan, a canal: PanamTacoaTaco" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H. inversion H.
  - intros H.
    vm_compute in H.
    discriminate.
Qed.