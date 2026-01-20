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

Parameter v_oe v_two v_one v_one_str v_list v_dict : Any.
Parameter i2 i1 : int.
Axiom IsInt_v_two : IsInt v_two i2.
Axiom IsInt_v_one : IsInt v_one i1.
Axiom NotInt_v_oe : forall n, ~ IsInt v_oe n.
Axiom NotInt_v_one_str : forall n, ~ IsInt v_one_str n.
Axiom NotInt_v_list : forall n, ~ IsInt v_list n.
Axiom NotInt_v_dict : forall n, ~ IsInt v_dict n.

Example test_case_mixed: filter_integers_spec [v_oe; v_two; v_one; v_one_str; v_list; v_dict] [i2; i1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - apply NotInt_v_oe.
  - eapply fir_cons_int.
    + apply IsInt_v_two.
    + eapply fir_cons_int.
      * apply IsInt_v_one.
      * eapply fir_cons_nonint.
        { apply NotInt_v_one_str. }
        eapply fir_cons_nonint.
        { apply NotInt_v_list. }
        eapply fir_cons_nonint.
        { apply NotInt_v_dict. }
        apply fir_nil.
Qed.