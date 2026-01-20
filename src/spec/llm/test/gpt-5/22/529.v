Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Parameter L_7_8_7_8_1 : Any.
Parameter V_1 : Any.
Parameter L_2_str3_1 : Any.
Parameter L_4 : Any.
Parameter L_7_8_7_8_2 : Any.
Parameter V_9 : Any.
Parameter L_7_8_7_8_3 : Any.
Parameter L_5_6 : Any.
Parameter L_2_str3_2 : Any.
Parameter L_7_8_7_8_4 : Any.

Axiom Hnonint_L_7_8_7_8_1 : forall n, ~ IsInt L_7_8_7_8_1 n.
Axiom HisInt_V_1 : IsInt V_1 1%Z.
Axiom Hnonint_L_2_str3_1 : forall n, ~ IsInt L_2_str3_1 n.
Axiom Hnonint_L_4 : forall n, ~ IsInt L_4 n.
Axiom Hnonint_L_7_8_7_8_2 : forall n, ~ IsInt L_7_8_7_8_2 n.
Axiom HisInt_V_9 : IsInt V_9 9%Z.
Axiom Hnonint_L_7_8_7_8_3 : forall n, ~ IsInt L_7_8_7_8_3 n.
Axiom Hnonint_L_5_6 : forall n, ~ IsInt L_5_6 n.
Axiom Hnonint_L_2_str3_2 : forall n, ~ IsInt L_2_str3_2 n.
Axiom Hnonint_L_7_8_7_8_4 : forall n, ~ IsInt L_7_8_7_8_4 n.

Example test_case_new:
  filter_integers_spec
    [L_7_8_7_8_1; V_1; L_2_str3_1; L_4; L_7_8_7_8_2; V_9; L_7_8_7_8_3; L_5_6; L_2_str3_2; L_7_8_7_8_4]
    [1%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply Hnonint_L_7_8_7_8_1|].
  eapply fir_cons_int; [apply HisInt_V_1|].
  eapply fir_cons_nonint; [apply Hnonint_L_2_str3_1|].
  eapply fir_cons_nonint; [apply Hnonint_L_4|].
  eapply fir_cons_nonint; [apply Hnonint_L_7_8_7_8_2|].
  eapply fir_cons_int; [apply HisInt_V_9|].
  eapply fir_cons_nonint; [apply Hnonint_L_7_8_7_8_3|].
  eapply fir_cons_nonint; [apply Hnonint_L_5_6|].
  eapply fir_cons_nonint; [apply Hnonint_L_2_str3_2|].
  eapply fir_cons_nonint; [apply Hnonint_L_7_8_7_8_4|].
  constructor.
Qed.