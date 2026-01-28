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

Example test_case : problem_85_spec [101%Z; 11%Z; 8%Z; 33%Z; 66%Z; 66%Z; 10%Z; 77%Z; 67%Z; 88%Z; 99%Z; 100%Z; 66%Z] 254%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 101, odd=false *)
  apply seao_other. left. reflexivity.
  (* Index 1: 11, odd=true, even=false *)
  apply seao_other. right. reflexivity.
  (* Index 2: 8, odd=false *)
  apply seao_other. left. reflexivity.
  (* Index 3: 33, odd=true, even=false *)
  apply seao_other. right. reflexivity.
  (* Index 4: 66, odd=false *)
  apply seao_other. left. reflexivity.
  (* Index 5: 66, odd=true, even=true -> Add 66 *)
  replace 254 with (66 + 188) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 6: 10, odd=false *)
  apply seao_other. left. reflexivity.
  (* Index 7: 77, odd=true, even=false *)
  apply seao_other. right. reflexivity.
  (* Index 8: 67, odd=false *)
  apply seao_other. left. reflexivity.
  (* Index 9: 88, odd=true, even=true -> Add 88 *)
  replace 188 with (88 + 100) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 10: 99, odd=false *)
  apply seao_other. left. reflexivity.
  (* Index 11: 100, odd=true, even=true -> Add 100 *)
  replace 100 with (100 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 12: 66, odd=false *)
  apply seao_other. left. reflexivity.
  (* End of list *)
  apply seao_nil.
Qed.