Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_odd_in_even_pos_aux (l : list Z) (idx : nat) : Z :=
  match l with
  | [] => 0%Z
  | h::t => (if (Nat.even idx) && Z.odd h then h else 0%Z) + sum_odd_in_even_pos_aux t (S idx)
  end.

Definition sum_odd_in_even_pos_impl (l : list Z) : Z := sum_odd_in_even_pos_aux l 0.

Definition problem_121_pre (l : list Z) : Prop := l <> [].

Definition problem_121_spec (l : list Z) (output : Z) : Prop :=
  output = sum_odd_in_even_pos_impl l.

Example problem_121_pre_holds :
  problem_121_pre [0%Z; 0%Z; 0%Z; 0%Z; -1%Z; 75%Z].
Proof.
  unfold problem_121_pre.
  intros H.
  discriminate H.
Qed.

Definition lZ := [0%Z; 0%Z; 0%Z; 0%Z; -1%Z; 75%Z].

Example problem_121_example_Z :
  problem_121_spec lZ (-1%Z).
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl, lZ.
  simpl.
  reflexivity.
Qed.