Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_37 : is_prime_spec 37 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    match goal with
    | |- prime 37 =>
        let val := constr:(prime_dec 37) in
        let res := eval vm_compute in val in
        match res with
        | left ?p => exact p
        | right _ => fail "37 is prime but prime_dec returned right"
        | _ => fail "prime_dec did not reduce"
        end
    end.
  - intros _.
    reflexivity.
Qed.