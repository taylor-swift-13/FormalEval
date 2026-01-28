Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope Z_scope.

Definition remove_duplicates_spec (numbers : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Nat.eqb (count_occ Z.eq_dec numbers x) 1) numbers.

Example test_case_new: remove_duplicates_spec 
  [1%Z; 6%Z; 2%Z; -5%Z; 3%Z; 16%Z; 1%Z; 3%Z; 4%Z; 5%Z; 7%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 3%Z; 12%Z; 15%Z; 16%Z; 18%Z; 19%Z; 20%Z; 18%Z; 10%Z; 12%Z; 7%Z; 3%Z; 14%Z; 16%Z; 10%Z; 18%Z; 19%Z; 20%Z; 7%Z; 19%Z; 10%Z; 20%Z; 18%Z; 12%Z; 16%Z; 18%Z] 
  [2%Z; -5%Z; 4%Z; 5%Z; 8%Z; 9%Z; 15%Z; 14%Z].
Proof.
  unfold remove_duplicates_spec.
  vm_compute.
  reflexivity.
Qed.