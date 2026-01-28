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

Example test_case : problem_85_spec [11; 22; 32; 54; 44; 55; 66; 77; 88; 66; 99; 100; 44; 22] 264.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Even index, skip. *)
  apply seao_other. left; reflexivity.
  (* Index 1: 22. Odd index, even value. Add 22. Remainder: 242. *)
  replace 264 with (22 + 242) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 2: 32. Even index, skip. *)
  apply seao_other. left; reflexivity.
  (* Index 3: 54. Odd index, even value. Add 54. Remainder: 188. *)
  replace 242 with (54 + 188) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 4: 44. Even index, skip. *)
  apply seao_other. left; reflexivity.
  (* Index 5: 55. Odd index, odd value. Skip. *)
  apply seao_other. right; reflexivity.
  (* Index 6: 66. Even index, skip. *)
  apply seao_other. left; reflexivity.
  (* Index 7: 77. Odd index, odd value. Skip. *)
  apply seao_other. right; reflexivity.
  (* Index 8: 88. Even index, skip. *)
  apply seao_other. left; reflexivity.
  (* Index 9: 66. Odd index, even value. Add 66. Remainder: 122. *)
  replace 188 with (66 + 122) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 10: 99. Even index, skip. *)
  apply seao_other. left; reflexivity.
  (* Index 11: 100. Odd index, even value. Add 100. Remainder: 22. *)
  replace 122 with (100 + 22) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 12: 44. Even index, skip. *)
  apply seao_other. left; reflexivity.
  (* Index 13: 22. Odd index, even value. Add 22. Remainder: 0. *)
  replace 22 with (22 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* End of list *)
  apply seao_nil.
Qed.