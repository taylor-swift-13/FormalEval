Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Fixpoint sum_odd_in_even_pos_aux (l : list nat) (idx : nat) : nat :=
  match l with
  | [] => 0
  | h::t => (if (Nat.even idx) && negb (Nat.even h) then h else 0) + sum_odd_in_even_pos_aux t (S idx)
  end.

Definition sum_odd_in_even_pos_impl (l : list nat) : nat := sum_odd_in_even_pos_aux l 0.

Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  output = sum_odd_in_even_pos_impl l.

Example problem_121_pre_holds :
  problem_121_pre [1; 2; 1; 2; 1; 0; 1; 1; 1; 1; 1; 1].
Proof.
  unfold problem_121_pre.
  intros H.
  discriminate H.
Qed.

Example problem_121_example_nat :
  problem_121_spec [1; 2; 1; 2; 1; 0; 1; 1; 1; 1; 1; 1] 6.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Definition lZ := [1%Z; 2%Z; 1%Z; 2%Z; 1%Z; 0%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z].
Definition l_nat := map Z.to_nat lZ.

Example problem_121_example_Z :
  Z.of_nat (sum_odd_in_even_pos_impl l_nat) = 6%Z.
Proof.
  unfold l_nat, lZ.
  unfold sum_odd_in_even_pos_impl.
  simpl.
  reflexivity.
Qed.