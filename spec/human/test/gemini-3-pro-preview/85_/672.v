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

Example test_case : problem_85_spec [11%Z; 22%Z; 33%Z; 66%Z; 68%Z; 67%Z; 77%Z; 920%Z; 88%Z; 99%Z; 100%Z] 1008%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0, Val 11: Even index, skip *)
  apply seao_other. left; reflexivity.
  (* Index 1, Val 22: Odd index, Even val, add. Sum 1008 = 22 + 986 *)
  replace 1008 with (22 + 986) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 2, Val 33: Even index, skip *)
  apply seao_other. left; reflexivity.
  (* Index 3, Val 66: Odd index, Even val, add. Sum 986 = 66 + 920 *)
  replace 986 with (66 + 920) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 4, Val 68: Even index, skip *)
  apply seao_other. left; reflexivity.
  (* Index 5, Val 67: Odd index, Odd val, skip *)
  apply seao_other. right; reflexivity.
  (* Index 6, Val 77: Even index, skip *)
  apply seao_other. left; reflexivity.
  (* Index 7, Val 920: Odd index, Even val, add. Sum 920 = 920 + 0 *)
  replace 920 with (920 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 8, Val 88: Even index, skip *)
  apply seao_other. left; reflexivity.
  (* Index 9, Val 99: Odd index, Odd val, skip *)
  apply seao_other. right; reflexivity.
  (* Index 10, Val 100: Even index, skip *)
  apply seao_other. left; reflexivity.
  (* Nil *)
  apply seao_nil.
Qed.