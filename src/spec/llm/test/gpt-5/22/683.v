Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
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

Parameter a2_z : Any.
Parameter a3_z : Any.
Parameter a_four : Any.
Parameter a_5_5_r : Any.
Parameter a_8_103551238465293_r : Any.
Parameter a5_z : Any.
Parameter a_seven : Any.
Parameter a_8_str : Any.
Parameter a_9_0_r_1 : Any.
Parameter a_9_0_r_2 : Any.
Parameter a_four_2 : Any.
Parameter a2_z_2 : Any.

Parameter i2_z : int.
Parameter i3_z : int.
Parameter i5_z : int.
Parameter i2_z_2 : int.

Axiom IsInt_a2_z : IsInt a2_z i2_z.
Axiom IsInt_a3_z : IsInt a3_z i3_z.
Axiom IsInt_a5_z : IsInt a5_z i5_z.
Axiom IsInt_a2_z_2 : IsInt a2_z_2 i2_z_2.

Axiom NonInt_a_four : forall n, ~ IsInt a_four n.
Axiom NonInt_a_5_5_r : forall n, ~ IsInt a_5_5_r n.
Axiom NonInt_a_8_103551238465293_r : forall n, ~ IsInt a_8_103551238465293_r n.
Axiom NonInt_a_seven : forall n, ~ IsInt a_seven n.
Axiom NonInt_a_8_str : forall n, ~ IsInt a_8_str n.
Axiom NonInt_a_9_0_r_1 : forall n, ~ IsInt a_9_0_r_1 n.
Axiom NonInt_a_9_0_r_2 : forall n, ~ IsInt a_9_0_r_2 n.
Axiom NonInt_a_four_2 : forall n, ~ IsInt a_four_2 n.

Example test_case_mixed:
  filter_integers_spec
    [a2_z; a3_z; a_four; a_5_5_r; a_8_103551238465293_r; a5_z; a_seven; a_8_str; a_9_0_r_1; a_9_0_r_2; a_four_2; a2_z_2]
    [i2_z; i3_z; i5_z; i2_z_2].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a2_z|].
  eapply fir_cons_int; [apply IsInt_a3_z|].
  eapply fir_cons_nonint; [apply NonInt_a_four|].
  eapply fir_cons_nonint; [apply NonInt_a_5_5_r|].
  eapply fir_cons_nonint; [apply NonInt_a_8_103551238465293_r|].
  eapply fir_cons_int; [apply IsInt_a5_z|].
  eapply fir_cons_nonint; [apply NonInt_a_seven|].
  eapply fir_cons_nonint; [apply NonInt_a_8_str|].
  eapply fir_cons_nonint; [apply NonInt_a_9_0_r_1|].
  eapply fir_cons_nonint; [apply NonInt_a_9_0_r_2|].
  eapply fir_cons_nonint; [apply NonInt_a_four_2|].
  eapply fir_cons_int; [apply IsInt_a2_z_2|].
  apply fir_nil.
Qed.