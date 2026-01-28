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
  problem_121_pre [11; 22; 33; 44; 65; 55; 66; 88; 99; 0; 22; 33; 88].
Proof.
  unfold problem_121_pre.
  intros H.
  discriminate H.
Qed.

Example problem_121_example_nat :
  problem_121_spec [11; 22; 33; 44; 65; 55; 66; 88; 99; 0; 22; 33; 88] 208.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  reflexivity.
Qed.

Open Scope Z_scope.

Definition lZ := [11%Z; 22%Z; 33%Z; 44%Z; 65%Z; 55%Z; 66%Z; 88%Z; 99%Z; 0%Z; 22%Z; 33%Z; 88%Z].
Definition l_nat := map Z.to_nat lZ.

Example problem_121_example_Z :
  Z.of_nat (sum_odd_in_even_pos_impl l_nat) = 208%Z.
Proof.
  unfold l_nat, lZ.
  unfold sum_odd_in_even_pos_impl.
  simpl.
  reflexivity.
Qed.