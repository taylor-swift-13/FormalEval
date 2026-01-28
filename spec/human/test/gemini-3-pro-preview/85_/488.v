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

Example test_case : problem_85_spec [16%Z; 44%Z; 15%Z; 4%Z; 6%Z; 26%Z; 11%Z; 13%Z; 15%Z; 16%Z] 90%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 16 (even index -> skip) *)
  apply seao_other. { left. simpl. reflexivity. }
  (* Index 1: 44 (odd index, even value -> add) *)
  replace 90%Z with (44 + 46)%Z by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  (* Index 2: 15 (even index -> skip) *)
  apply seao_other. { left. simpl. reflexivity. }
  (* Index 3: 4 (odd index, even value -> add) *)
  replace 46%Z with (4 + 42)%Z by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  (* Index 4: 6 (even index -> skip) *)
  apply seao_other. { left. simpl. reflexivity. }
  (* Index 5: 26 (odd index, even value -> add) *)
  replace 42%Z with (26 + 16)%Z by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  (* Index 6: 11 (even index -> skip) *)
  apply seao_other. { left. simpl. reflexivity. }
  (* Index 7: 13 (odd index, odd value -> skip) *)
  apply seao_other. { right. simpl. reflexivity. }
  (* Index 8: 15 (even index -> skip) *)
  apply seao_other. { left. simpl. reflexivity. }
  (* Index 9: 16 (odd index, even value -> add) *)
  replace 16%Z with (16 + 0)%Z by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  (* Base case *)
  apply seao_nil.
Qed.