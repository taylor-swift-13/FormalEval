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

Example test_case : problem_85_spec [3%Z; 5%Z; 7%Z; 9%Z; 2%Z; 6%Z; 187%Z; 10%Z; 556%Z; 3%Z; 187%Z; 920%Z; 42%Z; 37%Z; 30%Z; 7%Z; 8%Z; 187%Z; 7%Z; 3%Z] 936%Z.
Proof.
  unfold problem_85_spec.
  Ltac solve_other := apply seao_other; [ simpl; try (left; reflexivity); try (right; reflexivity) | ].
  
  (* Indices 0-4: [3; 5; 7; 9; 2]. None match (even index or odd value). *)
  do 5 solve_other.
  
  (* Index 5: 6. Odd index, even value. Accumulate 6. *)
  replace 936%Z with (6 + 930)%Z by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  
  (* Index 6: 187. Even index. *)
  solve_other.
  
  (* Index 7: 10. Odd index, even value. Accumulate 10. *)
  replace 930%Z with (10 + 920)%Z by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  
  (* Indices 8-10: [556; 3; 187]. None match. *)
  do 3 solve_other.
  
  (* Index 11: 920. Odd index, even value. Accumulate 920. *)
  replace 920%Z with (920 + 0)%Z by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  
  (* Indices 12-19: [42; 37; 30; 7; 8; 187; 7; 3]. None match. *)
  do 8 solve_other.
  
  (* End of list *)
  apply seao_nil.
Qed.