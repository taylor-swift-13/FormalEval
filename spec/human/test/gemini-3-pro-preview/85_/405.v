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

Example test_case : problem_85_spec [2%Z; 8%Z; 7%Z; 10%Z; 11%Z; 7%Z; 1%Z; 2%Z; 9%Z; 2%Z] 22%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other.
  - left. simpl. reflexivity.
  - replace 22 with (8 + 14) by reflexivity.
    apply seao_odd_even.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + apply seao_other.
      * left. simpl. reflexivity.
      * replace 14 with (10 + 4) by reflexivity.
        apply seao_odd_even.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- apply seao_other.
           ++ left. simpl. reflexivity.
           ++ apply seao_other.
              ** right. simpl. reflexivity.
              ** apply seao_other.
                 --- left. simpl. reflexivity.
                 --- replace 4 with (2 + 2) by reflexivity.
                     apply seao_odd_even.
                     +++ simpl. reflexivity.
                     +++ simpl. reflexivity.
                     +++ apply seao_other.
                         *** left. simpl. reflexivity.
                         *** replace 2 with (2 + 0) by reflexivity.
                             apply seao_odd_even.
                             ---- simpl. reflexivity.
                             ---- simpl. reflexivity.
                             ---- apply seao_nil.
Qed.