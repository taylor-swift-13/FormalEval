Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates : remove_duplicates_spec [12; 0; 2; 5; 0; 2; 3; 4; 2; 4; 4; 5; 5; 4; 2; 5; 4; 2; 5] [12; 3].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.