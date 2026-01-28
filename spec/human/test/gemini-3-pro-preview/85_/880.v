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

Example test_case : problem_85_spec [2; 4; 6; 17; 10; 8; 10; 12; 14; 16; 18; 20; 17; 24; 26; 28; 30; 17]%Z 112%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 2 (even index) *)
  apply seao_other; [left; reflexivity | ].
  (* Index 1: 4 (odd index, even value) -> sum 112 = 4 + 108 *)
  replace 112%Z with (4 + 108)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 2: 6 (even index) *)
  apply seao_other; [left; reflexivity | ].
  (* Index 3: 17 (odd index, odd value) *)
  apply seao_other; [right; reflexivity | ].
  (* Index 4: 10 (even index) *)
  apply seao_other; [left; reflexivity | ].
  (* Index 5: 8 (odd index, even value) -> sum 108 = 8 + 100 *)
  replace 108%Z with (8 + 100)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 6: 10 (even index) *)
  apply seao_other; [left; reflexivity | ].
  (* Index 7: 12 (odd index, even value) -> sum 100 = 12 + 88 *)
  replace 100%Z with (12 + 88)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 8: 14 (even index) *)
  apply seao_other; [left; reflexivity | ].
  (* Index 9: 16 (odd index, even value) -> sum 88 = 16 + 72 *)
  replace 88%Z with (16 + 72)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 10: 18 (even index) *)
  apply seao_other; [left; reflexivity | ].
  (* Index 11: 20 (odd index, even value) -> sum 72 = 20 + 52 *)
  replace 72%Z with (20 + 52)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 12: 17 (even index) *)
  apply seao_other; [left; reflexivity | ].
  (* Index 13: 24 (odd index, even value) -> sum 52 = 24 + 28 *)
  replace 52%Z with (24 + 28)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 14: 26 (even index) *)
  apply seao_other; [left; reflexivity | ].
  (* Index 15: 28 (odd index, even value) -> sum 28 = 28 + 0 *)
  replace 28%Z with (28 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 16: 30 (even index) *)
  apply seao_other; [left; reflexivity | ].
  (* Index 17: 17 (odd index, odd value) *)
  apply seao_other; [right; reflexivity | ].
  (* End of list *)
  apply seao_nil.
Qed.