Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Definition compute_pair (l : list Z) : (Z * Z) :=
  match l with
  | [n] => (n / 15, n mod 15 + 10)
  | _ => (0, 0)
  end.

Example test_compute_pair : compute_pair [123%Z] = (8%Z, 13%Z).
Proof.
  unfold compute_pair.
  simpl.
  reflexivity.
Qed.