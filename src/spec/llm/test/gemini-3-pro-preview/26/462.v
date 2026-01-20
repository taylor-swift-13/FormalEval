Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_remove_duplicates_1 : remove_duplicates_spec [1%Z; -10%Z; 1%Z; 1%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 5%Z; 4%Z; 5%Z; 999%Z; 5%Z; 18%Z; 4%Z; 4%Z; 1%Z] [-10%Z; 999%Z; 18%Z].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.