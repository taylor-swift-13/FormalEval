Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case: remove_duplicates_spec [7%Z; 1%Z; 3%Z; 2%Z; 1%Z; 4%Z; 5%Z; 7%Z; 6%Z; 7%Z; 18%Z; 9%Z; 10%Z; 3%Z; 12%Z; 14%Z; 16%Z; 18%Z; 19%Z; 20%Z; 18%Z; 12%Z; 7%Z; 3%Z; 14%Z; 16%Z; 10%Z; 18%Z; 19%Z; 20%Z; 7%Z; 10%Z; 20%Z; 16%Z; 18%Z; 16%Z] [2%Z; 4%Z; 5%Z; 6%Z; 9%Z].
Proof.
  unfold remove_duplicates_spec.
  simpl.
  reflexivity.
Qed.