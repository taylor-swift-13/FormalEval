Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

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

Parameter v_int1 v_str_one v_list123 v_dict_six1 v_int2 v_dict_six2 : Any.
Axiom isint_v_int1 : IsInt v_int1 2%Z.
Axiom notint_v_str_one : forall n, ~ IsInt v_str_one n.
Axiom notint_v_list123 : forall n, ~ IsInt v_list123 n.
Axiom notint_v_dict_six1 : forall n, ~ IsInt v_dict_six1 n.
Axiom isint_v_int2 : IsInt v_int2 2%Z.
Axiom notint_v_dict_six2 : forall n, ~ IsInt v_dict_six2 n.

Example test_case_mixed: filter_integers_spec [v_int1; v_str_one; v_list123; v_dict_six1; v_int2; v_dict_six2] [2%Z; 2%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - exact isint_v_int1.
  - eapply fir_cons_nonint.
    + exact notint_v_str_one.
    + eapply fir_cons_nonint.
      * exact notint_v_list123.
      * eapply fir_cons_nonint.
        { exact notint_v_dict_six1. }
        eapply fir_cons_int.
        { exact isint_v_int2. }
        eapply fir_cons_nonint.
        { exact notint_v_dict_six2. }
        constructor.
Qed.