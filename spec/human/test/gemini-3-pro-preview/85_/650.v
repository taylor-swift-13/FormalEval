Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_even_at_odd_indices_rel : list Z -> nat -> Z -> Prop :=
| seao_nil : forall i, sum_even_at_odd_indices_rel nil i 0%Z
| seao_odd_even : forall h t i s_tail, Nat.odd i = true -> Z.even h = true ->
    sum_even_at_odd_indices_rel t (S i) s_tail ->
    sum_even_at_odd_indices_rel (h :: t) i (h + s_tail)
| seao_other : forall h t i s_tail, (Nat.odd i = false \/ Z.even h = false) ->
    sum_even_at_odd_indices_rel t (S i) s_tail ->
    sum_even_at_odd_indices_rel (h :: t) i s_tail.

Definition problem_85_pre (lst : list Z) : Prop := lst <> []%list.

Definition problem_85_spec (lst : list Z) (output : Z) : Prop :=
  sum_even_at_odd_indices_rel lst 0%nat output.

Example test_case : problem_85_spec [11%Z; 22%Z; 33%Z; 66%Z; 44%Z; 67%Z; 77%Z; 88%Z; 99%Z] 176%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Odd index? False. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 1: 22. Odd index? True. Even value? True. Use seao_odd_even. *)
  replace 176 with (22 + 154) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 2: 33. Odd index? False. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 3: 66. Odd index? True. Even value? True. Use seao_odd_even. *)
  replace 154 with (66 + 88) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 4: 44. Odd index? False. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 5: 67. Odd index? True. Even value? False. Use seao_other. *)
  apply seao_other. { right. reflexivity. }
  (* Index 6: 77. Odd index? False. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 7: 88. Odd index? True. Even value? True. Use seao_odd_even. *)
  replace 88 with (88 + 0) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 8: 99. Odd index? False. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* End of list. *)
  apply seao_nil.
Qed.