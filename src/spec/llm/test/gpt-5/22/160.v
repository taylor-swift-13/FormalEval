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

Parameter v_list_str5_int6 : Any.
Parameter v_int7 : Any.
Parameter v_list_int2_str3 : Any.
Parameter n7 : int.

Axiom IsInt_v_int7 : IsInt v_int7 n7.
Axiom NonInt_v_list_str5_int6 : forall n, ~ IsInt v_list_str5_int6 n.
Axiom NonInt_v_list_int2_str3 : forall n, ~ IsInt v_list_int2_str3 n.

Example test_case_nested: filter_integers_spec [v_list_str5_int6; v_int7; v_list_int2_str3] [n7].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact NonInt_v_list_str5_int6.
  - eapply fir_cons_int.
    + exact IsInt_v_int7.
    + eapply fir_cons_nonint.
      * exact NonInt_v_list_int2_str3.
      * apply fir_nil.
Qed.