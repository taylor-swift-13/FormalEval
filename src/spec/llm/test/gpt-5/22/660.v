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

Parameters
  v_2Z v_3Z v_four v_5_5R v_8_103551238465293R v_5Z v_seven v_str8 v_9_0R1 v_9_0R2 v_four2 : Any.
Parameters i_2Z i_3Z i_5Z : int.

Axioms
  H_2Z : IsInt v_2Z i_2Z.
Axiom H_3Z : IsInt v_3Z i_3Z.
Axiom H_5Z : IsInt v_5Z i_5Z.
Axiom H_four : forall n, ~ IsInt v_four n.
Axiom H_5_5R : forall n, ~ IsInt v_5_5R n.
Axiom H_8_103551238465293R : forall n, ~ IsInt v_8_103551238465293R n.
Axiom H_seven : forall n, ~ IsInt v_seven n.
Axiom H_str8 : forall n, ~ IsInt v_str8 n.
Axiom H_9_0R1 : forall n, ~ IsInt v_9_0R1 n.
Axiom H_9_0R2 : forall n, ~ IsInt v_9_0R2 n.
Axiom H_four2 : forall n, ~ IsInt v_four2 n.

Example test_case_new:
  filter_integers_spec
    [v_2Z; v_3Z; v_four; v_5_5R; v_8_103551238465293R; v_5Z; v_seven; v_str8; v_9_0R1; v_9_0R2; v_four2]
    [i_2Z; i_3Z; i_5Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H_2Z|].
  eapply fir_cons_int; [apply H_3Z|].
  apply (fir_cons_nonint v_four); [apply H_four|].
  apply (fir_cons_nonint v_5_5R); [apply H_5_5R|].
  apply (fir_cons_nonint v_8_103551238465293R); [apply H_8_103551238465293R|].
  eapply fir_cons_int; [apply H_5Z|].
  apply (fir_cons_nonint v_seven); [apply H_seven|].
  apply (fir_cons_nonint v_str8); [apply H_str8|].
  apply (fir_cons_nonint v_9_0R1); [apply H_9_0R1|].
  apply (fir_cons_nonint v_9_0R2); [apply H_9_0R2|].
  apply (fir_cons_nonint v_four2); [apply H_four2|].
  apply fir_nil.
Qed.