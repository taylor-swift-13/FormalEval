Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.NArith.NArith Coq.Bool.Bool Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_transformed (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0%Z
  | h :: t =>
      let transformed :=
        if (Nat.modulo n 3 =? 0) then (h * h)
        else if andb (Nat.modulo n 4 =? 0) (negb (Nat.modulo n 3 =? 0)) then (h * h * h)
        else h in
      transformed + sum_transformed t (S n)
  end.

Definition sum_squares_impl (lst : list Z) : Z := sum_transformed lst 0%nat.

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (output : Z) : Prop :=
  output = sum_squares_impl lst.

Example test_sum_squares_1 :
  problem_142_spec [1%Z; 2%Z; 3%Z] 6%Z.
Proof.
  unfold problem_142_spec, sum_squares_impl.
  simpl.
  (* Index 0: 1, 0 mod 3 = 0, square: 1*1 = 1 *)
  (* Index 1: 2, 1 mod 3 <> 0, 1 mod 4 <> 0, unchanged: 2 *)
  (* Index 2: 3, 2 mod 3 <> 0, 2 mod 4 <> 0, unchanged: 3 *)
  lia.
Qed.