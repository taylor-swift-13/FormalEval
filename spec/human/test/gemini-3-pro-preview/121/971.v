Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_odd_in_even_pos_aux (l : list Z) (idx : Z) : Z :=
  match l with
  | [] => 0
  | h::t => (if (Z.even idx) && (Z.odd h) then h else 0) + sum_odd_in_even_pos_aux t (idx + 1)
  end.

Definition sum_odd_in_even_pos_impl (l : list Z) : Z := sum_odd_in_even_pos_aux l 0.

Definition problem_121_pre (l : list Z) : Prop := l <> [].

Definition problem_121_spec (l : list Z) (output : Z) : Prop :=
  output = sum_odd_in_even_pos_impl l.

Example test_problem_121 : problem_121_spec [1; 1; 2; 1; -1; 1; 6; 1; 66; 1; 1; 1] 1.
Proof.
  unfold problem_121_spec.
  unfold sum_odd_in_even_pos_impl.
  simpl.
  reflexivity.
Qed.