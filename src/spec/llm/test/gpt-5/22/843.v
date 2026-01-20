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

Parameter v61 : Any.
Parameter v_list13 : Any.
Parameter v_str4 : Any.
Parameter v_list565 : Any.
Parameter v7 : Any.

Axiom IsInt_v61 : IsInt v61 61%Z.
Axiom IsInt_v7 : IsInt v7 7%Z.
Axiom NonInt_v_list13 : forall n, ~ IsInt v_list13 n.
Axiom NonInt_v_str4 : forall n, ~ IsInt v_str4 n.
Axiom NonInt_v_list565 : forall n, ~ IsInt v_list565 n.

Example test_case_new: filter_integers_spec [v61; v_list13; v_str4; v_list565; v7; v_list565] [61%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [ exact IsInt_v61 | ].
  eapply fir_cons_nonint; [ exact NonInt_v_list13 | ].
  eapply fir_cons_nonint; [ exact NonInt_v_str4 | ].
  eapply fir_cons_nonint; [ exact NonInt_v_list565 | ].
  eapply fir_cons_int; [ exact IsInt_v7 | ].
  eapply fir_cons_nonint; [ exact NonInt_v_list565 | ].
  constructor.
Qed.