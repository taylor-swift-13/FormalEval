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

Example test_case : problem_85_spec [3%Z; 5%Z; 7%Z; 9%Z; 2%Z; 122%Z; 6%Z; 8%Z; 556%Z; 100%Z; 187%Z; 42%Z; 37%Z; 29%Z; 5%Z; 42%Z] 314%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 3. Even index. *)
  apply seao_other. left; reflexivity.
  (* Index 1: 5. Odd index, Odd value. *)
  apply seao_other. right; reflexivity.
  (* Index 2: 7. Even index. *)
  apply seao_other. left; reflexivity.
  (* Index 3: 9. Odd index, Odd value. *)
  apply seao_other. right; reflexivity.
  (* Index 4: 2. Even index. *)
  apply seao_other. left; reflexivity.
  (* Index 5: 122. Odd index, Even value. *)
  replace 314%Z with (122 + 192)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 6: 6. Even index. *)
  apply seao_other. left; reflexivity.
  (* Index 7: 8. Odd index, Even value. *)
  replace 192%Z with (8 + 184)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 8: 556. Even index. *)
  apply seao_other. left; reflexivity.
  (* Index 9: 100. Odd index, Even value. *)
  replace 184%Z with (100 + 84)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 10: 187. Even index. *)
  apply seao_other. left; reflexivity.
  (* Index 11: 42. Odd index, Even value. *)
  replace 84%Z with (42 + 42)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 12: 37. Even index. *)
  apply seao_other. left; reflexivity.
  (* Index 13: 29. Odd index, Odd value. *)
  apply seao_other. right; reflexivity.
  (* Index 14: 5. Even index. *)
  apply seao_other. left; reflexivity.
  (* Index 15: 42. Odd index, Even value. *)
  replace 42%Z with (42 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Nil *)
  apply seao_nil.
Qed.