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

Parameter a_apple a_real a_none a_neg2 a_42 : Any.
Parameter n42 : int.
Axiom H_apple_nonint : forall n, ~ IsInt a_apple n.
Axiom H_real_nonint : forall n, ~ IsInt a_real n.
Axiom H_none_nonint : forall n, ~ IsInt a_none n.
Axiom H_neg2_nonint : forall n, ~ IsInt a_neg2 n.
Axiom H_42_int : IsInt a_42 n42.

Example test_case_new: filter_integers_spec [a_apple; a_real; a_none; a_neg2; a_42] [n42].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact H_apple_nonint.
  - eapply fir_cons_nonint.
    + exact H_real_nonint.
    + eapply fir_cons_nonint.
      * exact H_none_nonint.
      * eapply fir_cons_nonint.
        -- exact H_neg2_nonint.
        -- eapply fir_cons_int.
           ++ exact H_42_int.
           ++ apply fir_nil.
Qed.