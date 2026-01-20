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

Parameter v_2_7 : Any.
Parameter v_3_0a : Any.
Parameter v_8_164599210590822 : Any.
Parameter v_1_5 : Any.
Parameter v_3_0b : Any.

Axiom not_int_v_2_7 : forall n, ~ IsInt v_2_7 n.
Axiom not_int_v_3_0a : forall n, ~ IsInt v_3_0a n.
Axiom not_int_v_8_164599210590822 : forall n, ~ IsInt v_8_164599210590822 n.
Axiom not_int_v_1_5 : forall n, ~ IsInt v_1_5 n.
Axiom not_int_v_3_0b : forall n, ~ IsInt v_3_0b n.

Example test_case_floats: filter_integers_spec [v_2_7; v_3_0a; v_8_164599210590822; v_1_5; v_3_0b] [].
Proof.
  unfold filter_integers_spec.
  constructor.
  - exact not_int_v_2_7.
  - constructor.
    + exact not_int_v_3_0a.
    + constructor.
      * exact not_int_v_8_164599210590822.
      * constructor.
        { exact not_int_v_1_5. }
        { constructor.
          { exact not_int_v_3_0b. }
          { constructor. } }
Qed.