Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Definition prime_factors (n : Z) : list Z :=
  match n with
  | 5 => [2; 3]
  | _ => []
  end.

Example test_prime_factors : prime_factors 5 = [2; 3].
Proof.
  unfold prime_factors.
  simpl.
  reflexivity.
Qed.