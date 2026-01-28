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

Example test_case : problem_85_spec [3%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 17%Z; 8%Z; 9%Z; 10%Z; 77%Z; 11%Z; 12%Z; 5%Z; 17%Z; 14%Z; 15%Z; 16%Z; 9%Z; 17%Z; 20%Z; 20%Z; 15%Z; 9%Z; 9%Z; 1%Z; 9%Z] 68%Z.
Proof.
  unfold problem_85_spec.
  repeat match goal with
  | [ |- sum_even_at_odd_indices_rel [] _ _ ] =>
      apply seao_nil
  | [ |- sum_even_at_odd_indices_rel (?h :: ?t) ?i ?s ] =>
      let o := eval compute in (Nat.odd i) in
      let e := eval compute in (Z.even h) in
      match o with
      | false => apply seao_other; [ left; reflexivity | ]
      | true =>
        match e with
        | false => apply seao_other; [ right; reflexivity | ]
        | true =>
          let rem := eval compute in (s - h) in
          replace s with (h + rem) by (vm_compute; reflexivity);
          apply seao_odd_even; [ reflexivity | reflexivity | ]
        end
      end
  end.
Qed.