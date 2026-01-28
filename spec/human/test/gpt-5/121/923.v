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

Open Scope Z_scope.

Definition lZ := [1%Z; 1%Z; 2%Z; 1%Z; (-1)%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z].
Definition l_nat := map Z.to_nat lZ.

Example problem_121_pre_holds :
  problem_121_pre l_nat.
Proof.
  unfold problem_121_pre, l_nat, lZ.
  simpl.
  intros H.
  discriminate H.
Qed.

Example problem_121_example_nat :
  problem_121_spec l_nat 4.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl, l_nat, lZ.
  simpl.
  reflexivity.
Qed.

Fixpoint sum_odd_in_even_pos_aux_Z (l : list Z) (idx : nat) : Z :=
  match l with
  | [] => 0%Z
  | h::t => (if (Nat.even idx) && Z.odd h then h else 0%Z) + sum_odd_in_even_pos_aux_Z t (S idx)
  end.

Definition sum_odd_in_even_pos_impl_Z (l : list Z) : Z := sum_odd_in_even_pos_aux_Z l 0.

Example problem_121_example_Z :
  sum_odd_in_even_pos_impl_Z lZ = 3%Z.
Proof.
  unfold lZ.
  unfold sum_odd_in_even_pos_impl_Z.
  simpl.
  reflexivity.
Qed.