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

Example test_case : problem_85_spec [3%Z; 7%Z; 4%Z; 1%Z; 9%Z; 10%Z] 10%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 3 (Odd index? No) -> Skip *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 1: 7 (Odd index? Yes, Even val? No) -> Skip *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 2: 4 (Odd index? No) -> Skip *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 3: 1 (Odd index? Yes, Even val? No) -> Skip *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 4: 9 (Odd index? No) -> Skip *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 5: 10 (Odd index? Yes, Even val? Yes) -> Add *)
  replace 10%Z with (10 + 0)%Z by reflexivity.
  apply seao_odd_even.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - apply seao_nil.
Qed.