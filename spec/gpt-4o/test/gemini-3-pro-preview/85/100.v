Require Import List.
Require Import Nat.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (lst : list Z) (s : Z) : Prop :=
  s = fold_left Z.add (filter Z.even (map (fun i => nth i lst 0) (map (fun k => (2 * k + 1)%nat) (seq 0%nat (length lst / 2)%nat)))) 0.

Example test_add_spec : add_spec [-64; -4; 5; -78] (-82).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.