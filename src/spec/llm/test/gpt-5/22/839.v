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

Parameters v0 v_str3 v4 v_reals v61 v_dict v_true v_false : Any.
Parameters n0 n4 n61 : int.
Axiom HIsInt_v0 : IsInt v0 n0.
Axiom HIsInt_v4 : IsInt v4 n4.
Axiom HIsInt_v61 : IsInt v61 n61.
Axiom HNotInt_str3 : forall n, ~ IsInt v_str3 n.
Axiom HNotInt_reals : forall n, ~ IsInt v_reals n.
Axiom HNotInt_dict : forall n, ~ IsInt v_dict n.
Axiom HNotInt_true : forall n, ~ IsInt v_true n.
Axiom HNotInt_false : forall n, ~ IsInt v_false n.

Example test_case_new: filter_integers_spec [v0; v_str3; v4; v_reals; v61; v_dict; v_true; v_false; v_dict] [n0; n4; n61].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - apply HIsInt_v0.
  - eapply fir_cons_nonint.
    + apply HNotInt_str3.
    + eapply fir_cons_int.
      * apply HIsInt_v4.
      * eapply fir_cons_nonint.
        { apply HNotInt_reals. }
        { eapply fir_cons_int.
          - apply HIsInt_v61.
          - eapply fir_cons_nonint.
            + apply HNotInt_dict.
            + eapply fir_cons_nonint.
              * apply HNotInt_true.
              * eapply fir_cons_nonint.
                { apply HNotInt_false. }
                { eapply fir_cons_nonint.
                  - apply HNotInt_dict.
                  - apply fir_nil.
                }
        }
Qed.