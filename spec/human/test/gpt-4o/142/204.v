Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.NArith.NArith Coq.Bool.Bool.
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_transformed (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0%Z
  | h :: t =>
      let transformed :=
        if (Nat.eqb (Nat.modulo n 3) 0%nat) then (Z.mul h h)
        else if andb (Nat.eqb (Nat.modulo n 4) 0%nat) (negb (Nat.eqb (Nat.modulo n 3) 0%nat)) then Z.mul (Z.mul h h) h
        else h in
      Z.add transformed (sum_transformed t (S n))
  end.

Definition sum_squares_impl (lst : list Z) : Z := sum_transformed lst 0%nat.

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (output : Z) : Prop :=
  output = sum_squares_impl lst.

Example problem_142_test_case_1 :
  problem_142_spec [3%Z; 6%Z; 2%Z; 1%Z; 7%Z; 8%Z; -9%Z; -3%Z; 4%Z; 11%Z; 11%Z] 643%Z.
Proof.
  unfold problem_142_spec.
  unfold sum_squares_impl.
  simpl.
  (* Calculate each step manually *)
  (* Index 0: 3^2 = 9 *)
  (* Index 1: 6 (unchanged) *)
  (* Index 2: 2 (unchanged) *)
  (* Index 3: 1 (unchanged) *)
  (* Index 4: 7 (unchanged) *)
  (* Index 5: 8 (unchanged) *)
  (* Index 6: (-9)^2 = 81 *)
  (* Index 7: (-3)^3 = -27 *)
  (* Index 8: 4^2 = 16 *)
  (* Index 9: 11^2 = 121 *)
  (* Index 10: 11 (unchanged) *)
  (* Sum = 9 + 6 + 2 + 1 + 7 + 8 + 81 - 27 + 16 + 121 + 11 = 643 *)
  reflexivity.
Qed.

Example problem_142_test_case_2 :
  problem_142_spec [] 0%Z.
Proof.
  unfold problem_142_spec.
  unfold sum_squares_impl.
  simpl.
  reflexivity.
Qed.

Example problem_142_test_case_3 :
  problem_142_spec [-1%Z; -5%Z; 2%Z; -1%Z; -5%Z] (-126%Z).
Proof.
  unfold problem_142_spec.
  unfold sum_squares_impl.
  simpl.
  (* Calculate each step manually *)
  (* Index 0: (-1)^2 = 1 *)
  (* Index 1: -5 (unchanged) *)
  (* Index 2: 2 (unchanged) *)
  (* Index 3: (-1)^3 = -1 *)
  (* Index 4: -5 (unchanged) *)
  (* Sum = 1 - 5 + 2 - 1 - 5 = -8 *)
  reflexivity.
Qed.