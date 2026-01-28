Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_odd_in_even_pos_aux (l : list Z) (idx : nat) : Z :=
  match l with
  | [] => 0
  | h::t => (if (Nat.even idx) && negb (Z.even h) then h else 0) + sum_odd_in_even_pos_aux t (S idx)
  end.

Definition sum_odd_in_even_pos_impl (l : list Z) : Z := sum_odd_in_even_pos_aux l 0.

Definition problem_121_pre (l : list Z) : Prop := l <> [].

Definition problem_121_spec (l : list Z) (output : Z) : Prop :=
  output = sum_odd_in_even_pos_impl l.

Example test_problem_121 : problem_121_spec [1; -2; 5; 0; -3] 3.
Proof.
  unfold problem_121_spec.
  unfold sum_odd_in_even_pos_impl.
  simpl.
  reflexivity.
Qed.