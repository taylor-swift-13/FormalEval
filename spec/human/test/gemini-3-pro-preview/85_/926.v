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

Example test_case : problem_85_spec [11%Z; 22%Z; 33%Z; 44%Z; 68%Z; 77%Z; 921%Z; 100%Z; 66%Z; 100%Z] 266%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other.
  - left. reflexivity.
  - replace 266 with (22 + 244) by reflexivity.
    apply seao_odd_even.
    + reflexivity.
    + reflexivity.
    + apply seao_other.
      * left. reflexivity.
      * replace 244 with (44 + 200) by reflexivity.
        apply seao_odd_even.
        -- reflexivity.
        -- reflexivity.
        -- apply seao_other.
           ++ left. reflexivity.
           ++ apply seao_other.
              ** right. reflexivity.
              ** apply seao_other.
                 --- left. reflexivity.
                 --- replace 200 with (100 + 100) by reflexivity.
                     apply seao_odd_even.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ apply seao_other.
                         *** left. reflexivity.
                         *** replace 100 with (100 + 0) by reflexivity.
                             apply seao_odd_even.
                             ---- reflexivity.
                             ---- reflexivity.
                             ---- apply seao_nil.
Qed.