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

Example test_case : problem_85_spec [1%Z; 4%Z; 5%Z; 2%Z; 3%Z; 8%Z; 7%Z; 17%Z; 6%Z; 9%Z; 23%Z; 2%Z; 9%Z; 17%Z; 2%Z; 2%Z] 18%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 1. Even index. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 1: 4. Odd index, Even value. Add 4. *)
  replace 18 with (4 + 14) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 2: 5. Even index. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 3: 2. Odd index, Even value. Add 2. *)
  replace 14 with (2 + 12) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 4: 3. Even index. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 5: 8. Odd index, Even value. Add 8. *)
  replace 12 with (8 + 4) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 6: 7. Even index. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 7: 17. Odd index, Odd value. *)
  apply seao_other; [right; reflexivity | ].
  (* Index 8: 6. Even index. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 9: 9. Odd index, Odd value. *)
  apply seao_other; [right; reflexivity | ].
  (* Index 10: 23. Even index. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 11: 2. Odd index, Even value. Add 2. *)
  replace 4 with (2 + 2) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 12: 9. Even index. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 13: 17. Odd index, Odd value. *)
  apply seao_other; [right; reflexivity | ].
  (* Index 14: 2. Even index. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 15: 2. Odd index, Even value. Add 2. *)
  replace 2 with (2 + 0) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Nil *)
  apply seao_nil.
Qed.