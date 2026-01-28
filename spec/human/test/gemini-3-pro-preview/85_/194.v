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

Example test_case : problem_85_spec [11%Z; 67%Z; 22%Z; 33%Z; 44%Z; 55%Z; 66%Z; 88%Z; 99%Z; 100%Z; 100%Z; 55%Z] 188%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11 (even index) *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 1: 67 (odd index, odd value) *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 2: 22 (even index) *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 3: 33 (odd index, odd value) *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 4: 44 (even index) *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 5: 55 (odd index, odd value) *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 6: 66 (even index) *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 7: 88 (odd index, even value) -> Add 88 *)
  replace 188%Z with (88 + 100)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  (* Index 8: 99 (even index) *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 9: 100 (odd index, even value) -> Add 100 *)
  replace 100%Z with (100 + 0)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  (* Index 10: 100 (even index) *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 11: 55 (odd index, odd value) *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 12: Nil *)
  apply seao_nil.
Qed.