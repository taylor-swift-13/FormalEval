Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_123456791 : is_prime_spec 123456791 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    match goal with
    | [ |- prime ?p ] =>
      let d := constr:(prime_dec p) in
      let res := eval vm_compute in d in
      match res with
      | left ?proof => exact proof
      | right _ => fail "Not a prime"
      end
    end.
  - intros _. reflexivity.
Qed.