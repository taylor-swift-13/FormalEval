Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.NArith.NArith Coq.Arith.PeanoNat Coq.Bool.Bool.
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_transformed (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0%Z
  | h :: t =>
      let transformed :=
        if Nat.eqb (Nat.modulo n 3%nat) 0%nat then (Z.mul h h)
        else if andb (Nat.eqb (Nat.modulo n 4%nat) 0%nat)
                     (negb (Nat.eqb (Nat.modulo n 3%nat) 0%nat))
             then Z.mul (Z.mul h h) h
             else h in
      Z.add transformed (sum_transformed t (S n))
  end.

Definition sum_squares_impl (lst : list Z) : Z := sum_transformed lst 0%nat.

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (output : Z) : Prop :=
  output = sum_squares_impl lst.

Example problem_142_test_case_1 :
  problem_142_spec [3%Z; 6%Z; 9%Z; 22%Z; 11%Z; 18%Z; 21%Z; 24%Z] 2322%Z.
Proof.
  unfold problem_142_spec.
  unfold sum_squares_impl.
  vm_compute.
  reflexivity.
Qed.